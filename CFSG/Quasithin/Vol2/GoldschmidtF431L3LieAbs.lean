module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3Datum
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpData
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComplementConjugacy

public section

namespace CFSG.Quasithin.H13.F431.L3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped Pointwise

section Split

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem conjSub_eq_of_normal_subgroup {Inn : Subgroup H} [Inn.Normal] (g : H) :
    conjSub g Inn = Inn := by
  ext x
  rw [mem_conjSub]
  constructor
  · intro h
    have := Subgroup.Normal.conj_mem inferInstance _ h g
    simpa [mul_assoc] using this
  · intro h
    have := Subgroup.Normal.conj_mem inferInstance _ h g⁻¹
    simpa using this

theorem exists_mem_normalizer_split {T B₀ Inn : Subgroup H} [Inn.Normal] (hTI : T ≤ Inn)
    (hBI : B₀ ≤ Inn) (hBN : B₀ ≤ Subgroup.normalizer (T : Set H))
    (hcard : Nat.card ↥(Subgroup.normalizer (T : Set H) ⊓ Inn) = Nat.card T * Nat.card B₀)
    (hcop : Nat.Coprime (Nat.card T) (Nat.card B₀)) {n : H}
    (hn : n ∈ Subgroup.normalizer (T : Set H)) :
    ∃ t ∈ T, t⁻¹ * n ∈ Subgroup.normalizer (B₀ : Set H) := by
  classical
  set N : Subgroup H := Subgroup.normalizer (T : Set H) with hN
  set N0 : Subgroup H := N ⊓ Inn with hN0
  have hTN0 : T ≤ N0 := le_inf Subgroup.le_normalizer hTI
  have hBN0 : B₀ ≤ N0 := le_inf hBN hBI
  have hKN0 : conjSub n B₀ ≤ N0 := by
    intro y hy
    rw [mem_conjSub] at hy
    refine ⟨?_, ?_⟩
    · have hb := hBN hy
      have h1 : n * (n⁻¹ * y * n) * n⁻¹ ∈ N := N.mul_mem (N.mul_mem hn hb) (N.inv_mem hn)
      simpa [mul_assoc] using h1
    · have hb := hBI hy
      have h1 := Subgroup.Normal.conj_mem inferInstance _ hb n
      simpa [mul_assoc] using h1
  set T' : Subgroup ↥N0 := T.subgroupOf N0 with hT'
  set B' : Subgroup ↥N0 := B₀.subgroupOf N0 with hB'
  set K' : Subgroup ↥N0 := (conjSub n B₀).subgroupOf N0 with hK'
  have hTnorm : T'.Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    exact inf_le_left
  have cT : Nat.card T' = Nat.card T := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN0).toEquiv
  have cB : Nat.card B' = Nat.card B₀ := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN0).toEquiv
  have cK : Nat.card K' = Nat.card B₀ := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN0).toEquiv, card_conjSub]
  have hcop' : Nat.Coprime (Nat.card T') (Nat.card B') := by rw [cT, cB]; exact hcop
  have hcopK : Nat.Coprime (Nat.card T') (Nat.card K') := by rw [cT, cK]; exact hcop
  have hcardG : Nat.card ↥N0 = Nat.card T * Nat.card B₀ := hcard
  have hC1 : T'.IsComplement' B' :=
    Subgroup.isComplement'_of_coprime (by rw [cT, cB, hcardG]) hcop'
  have hC2 : T'.IsComplement' K' :=
    Subgroup.isComplement'_of_coprime (by rw [cT, cK, hcardG]) hcopK
  have hidx : T'.index = Nat.card B₀ := by rw [hC1.symm.index_eq_card, cB]
  have hcopI : Nat.Coprime (Nat.card T') T'.index := by rw [hidx, cT]; exact hcop
  obtain ⟨t, ht⟩ := CFSG.GorensteinWalter.SchurZassenhaus.exists_mem_normal_conjugator_of_coprime
    T' B' K' hTnorm hC1 hC2 hcopI
  have htT : ((t : ↥N0) : H) ∈ T := Subgroup.mem_subgroupOf.mp t.2
  refine ⟨((t : ↥N0) : H), htT, ?_⟩
  have h1 : conjSub ((t : ↥N0) : H) B₀ = conjSub n B₀ := by
    have h2 := congrArg (Subgroup.map N0.subtype) ht
    rw [hK', Subgroup.map_subgroupOf_eq_of_le hKN0, Subgroup.map_map] at h2
    rw [h2]
    have hB0 : B₀ = Subgroup.map N0.subtype B' := (Subgroup.map_subgroupOf_eq_of_le hBN0).symm
    unfold conjSub
    conv_lhs => rw [hB0]
    rw [Subgroup.map_map]
    rfl
  apply mem_normalizer_of_conjSub_eq
  rw [conjSub_mul, ← h1]
  exact conjSub_conjSub_inv _ _

end Split

section Star

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem star_disjoint {T B₀ : Subgroup H} (hBN : B₀ ≤ Subgroup.normalizer (T : Set H))
    (hTB : ∀ x ∈ T, x ∈ B₀ → x = 1) (hC : ∀ x ∈ T, (∀ b ∈ B₀, x * b = b * x) → x = 1) {x : H}
    (hxT : x ∈ T) (hx : x ∈ Subgroup.normalizer (B₀ : Set H)) : x = 1 := by
  apply hC x hxT
  intro b hb
  have h1 : x * b * x⁻¹ ∈ B₀ := (Subgroup.mem_normalizer_iff.mp hx b).mp hb
  have h2 : x * b * x⁻¹ * b⁻¹ ∈ B₀ := B₀.mul_mem h1 (B₀.inv_mem hb)
  have h3 : b * x⁻¹ * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hBN hb) x⁻¹).mp (T.inv_mem hxT)
  have h4 : x * b * x⁻¹ * b⁻¹ ∈ T := by
    have := T.mul_mem hxT h3
    simpa [mul_assoc] using this
  have h5 := hTB _ h4 h2
  calc x * b = x * b * x⁻¹ * b⁻¹ * (b * x) := by group
    _ = b * x := by rw [h5, one_mul]

theorem star_mul {T B₀ Inn : Subgroup H} [Inn.Normal] (hTI : T ≤ Inn) (hBI : B₀ ≤ Inn)
    (hBN : B₀ ≤ Subgroup.normalizer (T : Set H))
    (hcard : Nat.card ↥(Subgroup.normalizer (T : Set H) ⊓ Inn) = Nat.card T * Nat.card B₀)
    (hcop : Nat.Coprime (Nat.card T) (Nat.card B₀)) {n : H}
    (hn : n ∈ Subgroup.normalizer (T : Set H)) :
    ∃ t ∈ T, ∃ b ∈ Subgroup.normalizer (T : Set H) ⊓ Subgroup.normalizer (B₀ : Set H),
      n = t * b := by
  obtain ⟨t, htT, hb⟩ := exists_mem_normalizer_split hTI hBI hBN hcard hcop hn
  refine ⟨t, htT, t⁻¹ * n, ⟨?_, hb⟩, by group⟩
  exact (Subgroup.normalizer (T : Set H)).mul_mem
    ((Subgroup.normalizer (T : Set H)).inv_mem (Subgroup.le_normalizer htT)) hn

omit [Finite H] in
theorem star_odd {T B₀ : Subgroup H} (hSyl : IsSylowTwoOf T ⊤)
    (hBN : B₀ ≤ Subgroup.normalizer (T : Set H)) (hTB : ∀ x ∈ T, x ∈ B₀ → x = 1)
    (hC : ∀ x ∈ T, (∀ b ∈ B₀, x * b = b * x) → x = 1)
    (hmul : ∀ n ∈ Subgroup.normalizer (T : Set H), ∃ t ∈ T,
      ∃ b ∈ Subgroup.normalizer (T : Set H) ⊓ Subgroup.normalizer (B₀ : Set H), n = t * b) :
    Odd (Nat.card ↥(Subgroup.normalizer (T : Set H) ⊓ Subgroup.normalizer (B₀ : Set H))) := by
  set N : Subgroup H := Subgroup.normalizer (T : Set H) with hN
  set Bs : Subgroup H := N ⊓ Subgroup.normalizer (B₀ : Set H) with hBs
  have hBsN : Bs ≤ N := inf_le_left
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hSylN : IsSylowTwoOf T N := F7.isSylowTwoOf_mono_right hSyl hTN le_top
  set T' : Subgroup ↥N := T.subgroupOf N with hT'
  set B' : Subgroup ↥N := Bs.subgroupOf N with hB'
  have hdis : Disjoint T' B' := by
    rw [Subgroup.disjoint_def]
    intro x hxT hxB
    have h1 : (x : H) ∈ T := Subgroup.mem_subgroupOf.mp hxT
    have h2 : (x : H) ∈ Bs := Subgroup.mem_subgroupOf.mp hxB
    exact Subtype.ext (star_disjoint hBN hTB hC h1 h2.2)
  have hmu : (T' : Set ↥N) * (B' : Set ↥N) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro n
    obtain ⟨t, ht, b, hb, hnb⟩ := hmul n n.2
    refine Set.mem_mul.mpr ⟨⟨t, hTN ht⟩, Subgroup.mem_subgroupOf.mpr ht, ⟨b, hBsN hb⟩,
      Subgroup.mem_subgroupOf.mpr hb, ?_⟩
    exact Subtype.ext hnb.symm
  have hcomp : T'.IsComplement' B' := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis hmu
  have hidx : T'.index = Nat.card B' := hcomp.symm.index_eq_card
  have hodd : ¬ 2 ∣ T'.index := F7.isSylowTwoOf_odd_relIndex hSylN
  rw [hidx] at hodd
  have hc : Nat.card B' = Nat.card Bs := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBsN).toEquiv
  rw [hc] at hodd
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)

theorem frattini_split {T M Inn : Subgroup H} [Inn.Normal] (hSyl : IsSylowTwoOf T ⊤) (hTM : T ≤ M)
    (hTI : T ≤ Inn) {m : H} (hm : m ∈ M) :
    ∃ x ∈ M ⊓ Inn, x⁻¹ * m ∈ Subgroup.normalizer (T : Set H) := by
  set M0 : Subgroup H := M ⊓ Inn with hM0
  have hTM0 : T ≤ M0 := le_inf hTM hTI
  have hS0 : IsSylowTwoOf T M0 := F7.isSylowTwoOf_mono_right hSyl hTM0 le_top
  have hcM : conjSub m M0 = M0 := by
    rw [hM0, conjSub_inf, conjSub_eq_of_normal_subgroup (Inn := Inn), conjSub_eq_of_mem_normalizer
      (Subgroup.le_normalizer hm)]
  have hS1 : IsSylowTwoOf (conjSub m T) M0 := by
    have := F7.isSylowTwoOf_conj hS0 m
    rwa [hcM] at this
  obtain ⟨x, hx, hxT⟩ := IsSylowTwoOf.exists_conj hS0 hS1
  refine ⟨x, hx, ?_⟩
  apply mem_normalizer_of_conjSub_eq
  rw [conjSub_mul, show conjSub m T = conjSub x T from hxT]
  exact conjSub_conjSub_inv _ _

omit [Finite H] in
theorem star_stable {T B₀ M : Subgroup H} {s : H} (hNM : Subgroup.normalizer (T : Set H) ≤ M)
    (hsM : s ∈ M) (hsN : s ∉ Subgroup.normalizer (T : Set H))
    (hsB : s ∈ Subgroup.normalizer (B₀ : Set H)) (hBN : B₀ ≤ Subgroup.normalizer (T : Set H))
    (hSyl : IsSylowTwoOf T M)
    (hs : ∀ T'' : Subgroup H, IsSylowTwoOf T'' M → B₀ ≤ Subgroup.normalizer (T'' : Set H) →
      T'' = T ∨ T'' = conjSub s T) {b : H}
    (hb : b ∈ Subgroup.normalizer (T : Set H) ⊓ Subgroup.normalizer (B₀ : Set H)) :
    s⁻¹ * b * s ∈ Subgroup.normalizer (T : Set H) ⊓ Subgroup.normalizer (B₀ : Set H) := by
  obtain ⟨hbT, hbB⟩ := hb
  have hbM : b ∈ M := hNM hbT
  obtain ⟨g, hg⟩ : ∃ g : H, g = b * s := ⟨_, rfl⟩
  have hgM : g ∈ M := hg ▸ M.mul_mem hbM hsM
  have hS1 : IsSylowTwoOf (conjSub g T) M := by
    have := F7.isSylowTwoOf_conj hSyl g
    rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hgM)] at this
  have hinvB : ∀ c ∈ B₀, ∀ y ∈ Subgroup.normalizer (B₀ : Set H), y⁻¹ * c * y ∈ B₀ := by
    intro c hc y hy
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (B₀ : Set H)).inv_mem hy) c).mp
      hc
    simpa using this
  have hBT' : B₀ ≤ Subgroup.normalizer ((conjSub g T : Subgroup H) : Set H) := by
    intro c hc
    apply mem_normalizer_of_conjSub_eq
    have hc'' : s⁻¹ * (b⁻¹ * c * b) * s ∈ B₀ := hinvB _ (hinvB c hc b hbB) s hsB
    have e : c * g = g * (s⁻¹ * (b⁻¹ * c * b) * s) := by rw [hg]; group
    have h2 : conjSub c (conjSub g T) = conjSub (g * (s⁻¹ * (b⁻¹ * c * b) * s)) T := by
      rw [← conjSub_mul, e]
    rw [h2, conjSub_mul, conjSub_eq_of_mem_normalizer (hBN hc'')]
  rcases hs _ hS1 hBT' with h | h
  · exfalso
    have hgN : g ∈ Subgroup.normalizer (T : Set H) := mem_normalizer_of_conjSub_eq h
    apply hsN
    have := (Subgroup.normalizer (T : Set H)).mul_mem
      ((Subgroup.normalizer (T : Set H)).inv_mem hbT) hgN
    simpa [hg] using this
  · refine ⟨?_, ?_⟩
    · apply mem_normalizer_of_conjSub_eq
      have : conjSub (s⁻¹ * b * s) T = conjSub s⁻¹ (conjSub g T) := by
        rw [← conjSub_mul]; congr 1; rw [hg]; group
      rw [this, h, conjSub_conjSub_inv]
    · have h1 := (Subgroup.normalizer (B₀ : Set H)).mul_mem
        ((Subgroup.normalizer (B₀ : Set H)).inv_mem hsB) hbB
      exact (Subgroup.normalizer (B₀ : Set H)).mul_mem h1 hsB

theorem sylow_eq_of_centralizes {T M N Z : Subgroup H} (hSyl : IsSylowTwoOf T M)
    (hNT : ∀ X : Subgroup H, X ≤ N → IsPGroup 2 X → X ≤ T) (hZne : ∃ x ∈ Z, x ≠ 1)
    (hcent : ∀ x ∈ Z, x ≠ 1 → ∀ y ∈ M, y * x = x * y → y ∈ N) {T₁ : Subgroup H}
    (hT₁ : IsSylowTwoOf T₁ M) (hcz : ∀ t ∈ T₁, ∀ z ∈ Z, t * z = z * t) : T₁ = T := by
  obtain ⟨x, hxZ, hx1⟩ := hZne
  have hT₁N : T₁ ≤ N := fun y hy => hcent x hxZ hx1 y (hT₁.1 hy) (hcz y hy x hxZ)
  have hT₁T : T₁ ≤ T := hNT T₁ hT₁N hT₁.2.1
  exact (eq_of_isSylowTwoOf_of_isPGroup hT₁ hT₁T hSyl.1 hSyl.2.1).symm

theorem sylow_cases {T M N Z B₀ : Subgroup H} {s : H} (hSyl : IsSylowTwoOf T M)
    (hNT : ∀ X : Subgroup H, X ≤ N → IsPGroup 2 X → X ≤ T) (hZ : Z = centerOf T)
    (hZne : ∃ x ∈ Z, x ≠ 1) (hcent : ∀ x ∈ Z, x ≠ 1 → ∀ y ∈ M, y * x = x * y → y ∈ N)
    (hsM : s ∈ M)
    (hfix : ∀ m ∈ M, (∀ c ∈ B₀, ∀ z ∈ conjSub m Z, c * z * c⁻¹ ∈ conjSub m Z) →
      conjSub m Z = Z ∨ conjSub m Z = conjSub s Z) {T'' : Subgroup H}
    (hT'' : IsSylowTwoOf T'' M) (hB : B₀ ≤ Subgroup.normalizer (T'' : Set H)) :
    T'' = T ∨ T'' = conjSub s T := by
  have hZcent : ∀ {X : Subgroup H}, ∀ t ∈ X, ∀ z ∈ centerOf X, t * z = z * t := by
    intro X t ht z hz
    exact (mem_centerOf_iff.mp hz).2 t ht
  obtain ⟨g, hgM, hgT⟩ := IsSylowTwoOf.exists_conj hSyl hT''
  have hT''eq : T'' = conjSub g T := hgT
  have hZ'' : conjSub g Z = centerOf T'' := by rw [hZ, hT''eq, centerOf_conjSub]
  have hstab : ∀ c ∈ B₀, ∀ z ∈ conjSub g Z, c * z * c⁻¹ ∈ conjSub g Z := by
    intro c hc z hz
    rw [hZ'']
    rw [hZ''] at hz
    have h1 : c * z * c⁻¹ ∈ conjSub c (centerOf T'') := mul_mem_conjSub hz
    rwa [← centerOf_conjSub, conjSub_eq_of_mem_normalizer (hB hc)] at h1
  rcases hfix g hgM hstab with h | h
  · left
    refine sylow_eq_of_centralizes hSyl hNT hZne hcent hT'' ?_
    intro t ht z hz
    have : z ∈ centerOf T'' := by rw [← hZ'', h]; exact hz
    exact hZcent t ht z this
  · right
    have hs1M : s⁻¹ ∈ M := M.inv_mem hsM
    have hT₁ : IsSylowTwoOf (conjSub s⁻¹ T'') M := by
      have := F7.isSylowTwoOf_conj hT'' s⁻¹
      rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hs1M)] at this
    have hZ₁ : Z = centerOf (conjSub s⁻¹ T'') := by
      rw [centerOf_conjSub, ← hZ'', h, conjSub_conjSub_inv]
    have hT₁T : conjSub s⁻¹ T'' = T := by
      refine sylow_eq_of_centralizes hSyl hNT hZne hcent hT₁ ?_
      intro t ht z hz
      have : z ∈ centerOf (conjSub s⁻¹ T'') := by rw [← hZ₁]; exact hz
      exact hZcent t ht z this
    rw [← hT₁T, conjSub_inv_conjSub]

end Star

section FrameMap

variable {P H : Type} [Group P] [Group H] (Φ : P →* H) (hΦ : Function.Injective Φ)
include hΦ

theorem Frame.map {S Q₁ Q₂ : Subgroup P} (F : Frame S Q₁ Q₂) :
    Frame (S.map Φ) (Q₁.map Φ) (Q₂.map Φ) := by
  have hcen : centerOf (S.map Φ) = (centerOf S).map Φ := centerOf_map_of_injective Φ hΦ S
  have hmem : ∀ (X : Subgroup P) (a : P), Φ a ∈ X.map Φ ↔ a ∈ X := fun X a =>
    Subgroup.mem_map_iff_mem hΦ
  have hcard : ∀ X : Subgroup P, Nat.card (X.map Φ) = Nat.card X := fun X =>
    Subgroup.card_map_of_injective hΦ
  have hea : ∀ X : Subgroup P, IsElemAbelian 2 X → IsElemAbelian 2 (X.map Φ) := by
    intro X hX
    rw [F7.isElemAbelian_iff] at hX ⊢
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hX.1 a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hX.2 a ha, map_one]
  refine ⟨Subgroup.map_mono F.Q₁_le, Subgroup.map_mono F.Q₂_le, hea _ F.Q₁_ea, hea _ F.Q₂_ea,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_inf_eq _ _ Φ hΦ, F.inter, hcen]
  · rw [hcard, hcard, F.card_eq]
  · rw [hcard]; exact F.four_le
  · intro h
    exact F.Q_ne (Subgroup.map_injective hΦ h)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [hcen]
    refine ⟨a * b * a⁻¹ * b⁻¹, F.comm a ha b hb, by simp [map_mul, map_inv]⟩
  · rintro _ ⟨a, ha, rfl⟩ h2 h1
    have h1' : a ≠ 1 := fun h => h1 (by rw [h, map_one])
    have h2' : a ^ 2 = 1 := hΦ (by rw [map_pow, map_one]; exact h2)
    rcases F.inv a ha h2' h1' with h | h
    · exact Or.inl (Subgroup.mem_map_of_mem Φ h)
    · exact Or.inr (Subgroup.mem_map_of_mem Φ h)
  · rintro _ ⟨a, ha, rfl⟩ hxZ _ ⟨b, hb, rfl⟩ hxy
    have haZ : a ∉ centerOf S := fun h => hxZ (by rw [hcen]; exact Subgroup.mem_map_of_mem Φ h)
    have hab : b * a = a * b := hΦ (by rw [map_mul, map_mul]; exact hxy)
    exact Subgroup.mem_map_of_mem Φ (F.cent₁ a ha haZ b hb hab)
  · rintro _ ⟨a, ha, rfl⟩ hxZ _ ⟨b, hb, rfl⟩ hxy
    have haZ : a ∉ centerOf S := fun h => hxZ (by rw [hcen]; exact Subgroup.mem_map_of_mem Φ h)
    have hab : b * a = a * b := hΦ (by rw [map_mul, map_mul]; exact hxy)
    exact Subgroup.mem_map_of_mem Φ (F.cent₂ a ha haZ b hb hab)
  · intro A hA hAe hcardA
    have hAr : A ≤ Φ.range := hA.trans (Subgroup.map_le_range Φ S)
    have hAeq : (A.comap Φ).map Φ = A := by
      rw [Subgroup.map_comap_eq, inf_of_le_right hAr]
    have hA' : A.comap Φ ≤ S := by
      intro a ha
      have : Φ a ∈ S.map Φ := hA ha
      exact (hmem S a).mp this
    have hAe' : IsElemAbelian 2 (A.comap Φ) := by
      rw [F7.isElemAbelian_iff] at hAe ⊢
      refine ⟨fun a ha b hb => hΦ ?_, fun a ha => hΦ ?_⟩
      · rw [map_mul, map_mul]; exact hAe.1 _ ha _ hb
      · rw [map_pow, map_one]; exact hAe.2 _ ha
    have hc : Nat.card Q₁ ≤ Nat.card (A.comap Φ) := by
      have h1 : Nat.card ((A.comap Φ).map Φ) = Nat.card (A.comap Φ) := hcard _
      rw [hAeq, ← h1] at *
      rw [hcard] at hcardA
      exact hcardA
    rcases F.maxea _ hA' hAe' hc with h | h
    · left; rw [← hAeq, h]
    · right; rw [← hAeq, h]

end FrameMap

section ShapeOfFrame

variable {G : Type} [Group G] [Finite G]

theorem Frame.toSpShape {S Q₁ Q₂ : Subgroup G} (F : Frame S Q₁ Q₂)
    (h1 : S ≤ Subgroup.normalizer (Q₁ : Set G)) (h2 : S ≤ Subgroup.normalizer (Q₂ : Set G)) :
    SpShape S ![Q₁, Q₂] := by
  have hex : ∀ {A B : Subgroup G}, Frame S A B → ∃ x ∈ A, x ∉ centerOf S ∧ x ^ 2 = 1 := by
    intro A B F'
    by_contra hcon
    have hAZ : A ≤ centerOf S := by
      intro x hx
      by_contra hxZ
      exact hcon ⟨x, hx, hxZ, F7.isElemAbelian_pow_eq_one F'.Q₁_ea hx⟩
    have hAB : A ≤ B := by
      intro x hx
      have := hAZ hx
      rw [← F'.inter] at this
      exact this.2
    have : A = B := Subgroup.eq_of_le_of_card_ge hAB (le_of_eq F'.card_eq.symm)
    exact F'.Q_ne this
  have hZ : centerOf S ≤ Q₁ := by rw [← F.inter]; exact inf_le_left
  have hZ' : centerOf S ≤ Q₂ := by rw [← F.inter]; exact inf_le_right
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; fin_cases j
    · exact F.Q₁_le
    · exact F.Q₂_le
  · intro j; fin_cases j
    · exact h1
    · exact h2
  · intro j; fin_cases j
    · intro x hx y hy
      exact F7.isElemAbelian_comm F.Q₁_ea hx hy
    · intro x hx y hy
      exact F7.isElemAbelian_comm F.Q₂_ea hx hy
  · intro j; fin_cases j
    · exact hZ
    · exact hZ'
  · intro z hz
    exact F7.isElemAbelian_pow_eq_one F.Q₁_ea (hZ hz)
  · intro x hx hx2
    by_cases h1 : x = 1
    · exact ⟨0, by rw [h1]; exact Q₁.one_mem⟩
    · rcases F.inv x hx hx2 h1 with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  · intro j; fin_cases j
    · intro x hx hxZ y hy hxy
      exact F.cent₁ x hx hxZ y hy hxy
    · intro x hx hxZ y hy hxy
      exact F.cent₂ x hx hxZ y hy hxy
  · intro j; fin_cases j
    · exact hex F
    · exact hex F.symm

end ShapeOfFrame

section Structures

open CFSG.QuasithinUnique.Borel252

structure L3Half {P : Type} [Group P] (U R R' B₀ : Subgroup P) (s : P) : Prop where
  s_mem : s ∈ Subgroup.normalizer (R : Set P)
  s_not : s ∉ Subgroup.normalizer (R' : Set P)
  s_sq : s * s = 1
  s_norm : ∀ b ∈ B₀, s * b * s⁻¹ ∈ B₀
  cov : ∀ x ∈ R, x ≠ 1 → ∃ m ∈ Subgroup.normalizer (R : Set P), m * x * m⁻¹ ∈ centerOf U
  nonsolv : ¬ Group.IsSolvable ↥(Subgroup.normalizer (R : Set P))
  fix : ∀ m ∈ Subgroup.normalizer (R : Set P),
    (∀ c ∈ B₀, ∀ z ∈ conjSub m (centerOf U), c * z * c⁻¹ ∈ conjSub m (centerOf U)) →
    conjSub m (centerOf U) = centerOf U ∨ conjSub m (centerOf U) = conjSub s (centerOf U)

structure L3DData {P : Type} [Group P] (U R₁ R₂ B₀ : Subgroup P) (s₁ s₂ : P) : Prop where
  borel : BorelData P U R₁ R₂
  frame : Frame U R₁ R₂
  B₀_le : B₀ ≤ Subgroup.normalizer (U : Set P)
  B₀_odd : Odd (Nat.card B₀)
  mul : ∀ h ∈ Subgroup.normalizer (U : Set P), ∃ u ∈ U, ∃ b ∈ B₀, h = u * b
  trans : ∀ x ∈ centerOf U, x ≠ 1 → ∀ y ∈ centerOf U, y ≠ 1 → ∃ b ∈ B₀, b * x * b⁻¹ = y
  centS : ∀ x ∈ U, (∀ b ∈ B₀, x * b = b * x) → x = 1
  cent : ∀ x ∈ centerOf U, x ≠ 1 →
    Subgroup.centralizer ({x} : Set P) ≤ Subgroup.normalizer (U : Set P)
  half₁ : L3Half U R₁ R₂ B₀ s₁
  half₂ : L3Half U R₂ R₁ B₀ s₂
  rot : (s₁ * s₂) ^ 3 = 1
  Z_big : ∃ x ∈ centerOf U, ∃ y ∈ centerOf U, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y

theorem borelData_swap {M : Type} [Group M] {U R₁ R₂ : Subgroup M} (h : BorelData M U R₁ R₂) :
    BorelData M U R₂ R₁ where
  center_trivial := h.center_trivial
  sylow := h.sylow
  le₁ := h.le₂
  le₂ := h.le₁
  sup := by rw [sup_comm]; exact h.sup
  cent₁ := h.cent₂
  cent₂ := h.cent₁
  lt₁ := h.lt₂
  lt₂ := h.lt₁
  lt_top₁ := h.lt_top₂
  lt_top₂ := h.lt_top₁
  core₁ := h.core₂
  core₂ := h.core₁
  only := fun X hX hXt => (h.only X hX hXt).symm

theorem L3DData.swap {P : Type} [Group P] {U R₁ R₂ B₀ : Subgroup P} {s₁ s₂ : P}
    (h : L3DData U R₁ R₂ B₀ s₁ s₂) : L3DData U R₂ R₁ B₀ s₂ s₁ where
  borel := borelData_swap h.borel
  frame := h.frame.symm
  B₀_le := h.B₀_le
  B₀_odd := h.B₀_odd
  mul := h.mul
  trans := h.trans
  centS := h.centS
  cent := h.cent
  half₁ := h.half₂
  half₂ := h.half₁
  rot := by
    have e : (s₂ * s₁) ^ 3 = ((s₁ * s₂)⁻¹) ^ 3 := by
      have h1 : s₂ * s₁ = (s₁ * s₂)⁻¹ := by
        have hs1 : s₁ * s₁ = 1 := h.half₁.s_sq
        have hs2 : s₂ * s₂ = 1 := h.half₂.s_sq
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hs1, inv_eq_of_mul_eq_one_right hs2]
      rw [h1]
    rw [e, inv_pow, h.rot, inv_one]
  Z_big := h.Z_big

end Structures

section Lift

open CFSG.LieType.BorelTits CFSG.QuasithinUnique.Borel252

variable {P H : Type} [Group P] [Group H]

theorem card_eq_mul_of_split [Finite P] {N U B₀ : Subgroup P} (hUN : U ≤ N) (hBN : B₀ ≤ N)
    (hdis : ∀ x ∈ U, x ∈ B₀ → x = 1) (hmul : ∀ h ∈ N, ∃ u ∈ U, ∃ b ∈ B₀, h = u * b) :
    Nat.card N = Nat.card U * Nat.card B₀ := by
  set U' : Subgroup ↥N := U.subgroupOf N with hU'
  set B' : Subgroup ↥N := B₀.subgroupOf N with hB'
  have hd : Disjoint U' B' := by
    rw [Subgroup.disjoint_def]
    intro x hxU hxB
    exact Subtype.ext (hdis _ (Subgroup.mem_subgroupOf.mp hxU) (Subgroup.mem_subgroupOf.mp hxB))
  have hm : (U' : Set ↥N) * (B' : Set ↥N) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro n
    obtain ⟨u, hu, b, hb, hnb⟩ := hmul n n.2
    refine Set.mem_mul.mpr ⟨⟨u, hUN hu⟩, Subgroup.mem_subgroupOf.mpr hu, ⟨b, hBN hb⟩,
      Subgroup.mem_subgroupOf.mpr hb, ?_⟩
    exact Subtype.ext hnb.symm
  have hc : U'.IsComplement' B' := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hd hm
  have h := hc.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv] at h
  exact h.symm

theorem conjSub_map_apply (Φ : P →* H) (p : P) (X : Subgroup P) :
    conjSub (Φ p) (X.map Φ) = (conjSub p X).map Φ := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem le_of_le_normalizer_of_pgroup [Finite H] {T : Subgroup H} (hSyl : IsSylowTwoOf T ⊤)
    {X : Subgroup H} (hX : X ≤ Subgroup.normalizer (T : Set H)) (hXp : IsPGroup 2 X) : X ≤ T := by
  have hSylN : IsSylowTwoOf T (Subgroup.normalizer (T : Set H)) :=
    F7.isSylowTwoOf_mono_right hSyl Subgroup.le_normalizer le_top
  obtain ⟨x, hx, hXx⟩ := F7.isSylowTwoOf_exists_conj_le hSylN hX hXp
  rwa [conjSub_eq_of_mem_normalizer hx] at hXx

theorem fix_transport [Finite H] (Φ : P →* H) (hΦ : Function.Injective Φ) [Φ.range.Normal]
    {U R B₀ : Subgroup P} {s : P} (hSyl : IsSylowTwoOf (U.map Φ) ⊤)
    (hUR : U ≤ Subgroup.normalizer (R : Set P))
    (hfix : ∀ m ∈ Subgroup.normalizer (R : Set P),
      (∀ c ∈ B₀, ∀ z ∈ conjSub m (centerOf U), c * z * c⁻¹ ∈ conjSub m (centerOf U)) →
      conjSub m (centerOf U) = centerOf U ∨ conjSub m (centerOf U) = conjSub s (centerOf U)) :
    ∀ m ∈ Subgroup.normalizer ((R.map Φ : Subgroup H) : Set H),
      (∀ c ∈ B₀.map Φ, ∀ z ∈ conjSub m (centerOf (U.map Φ)),
        c * z * c⁻¹ ∈ conjSub m (centerOf (U.map Φ))) →
      conjSub m (centerOf (U.map Φ)) = centerOf (U.map Φ) ∨
        conjSub m (centerOf (U.map Φ)) = conjSub (Φ s) (centerOf (U.map Φ)) := by
  intro m hm hstab
  have hTM : U.map Φ ≤ Subgroup.normalizer ((R.map Φ : Subgroup H) : Set H) := by
    rintro _ ⟨u, hu, rfl⟩
    exact map_mem_normalizer_map Φ (hUR hu)
  have hTI : U.map Φ ≤ Φ.range := Subgroup.map_le_range Φ U
  obtain ⟨x, hx, hxm⟩ := frattini_split hSyl hTM hTI hm
  have hx' : x ∈ (Subgroup.normalizer (R : Set P)).map Φ := by
    rw [← normalizer_map_inf_range Φ hΦ R]; exact hx
  obtain ⟨p, hp, rfl⟩ := hx'
  have hcen : centerOf (U.map Φ) = (centerOf U).map Φ := centerOf_map_of_injective Φ hΦ U
  have hn : conjSub ((Φ p)⁻¹ * m) (centerOf (U.map Φ)) = centerOf (U.map Φ) := by
    rw [← centerOf_conjSub]
    congr 1
    exact conjSub_eq_of_mem_normalizer hxm
  have hmx : conjSub m (centerOf (U.map Φ)) = (conjSub p (centerOf U)).map Φ := by
    have : m = Φ p * ((Φ p)⁻¹ * m) := by group
    conv_lhs => rw [this, conjSub_mul, hn, hcen, conjSub_map_apply]
  have hstab' : ∀ c ∈ B₀, ∀ z ∈ conjSub p (centerOf U), c * z * c⁻¹ ∈ conjSub p (centerOf U) := by
    intro c hc z hz
    have h1 : Φ z ∈ conjSub m (centerOf (U.map Φ)) := by
      rw [hmx]; exact Subgroup.mem_map_of_mem Φ hz
    have h2 := hstab (Φ c) (Subgroup.mem_map_of_mem Φ hc) _ h1
    rw [hmx] at h2
    have h3 : Φ (c * z * c⁻¹) ∈ (conjSub p (centerOf U)).map Φ := by
      simpa [map_mul, map_inv] using h2
    exact (Subgroup.mem_map_iff_mem hΦ).mp h3
  rcases hfix p hp hstab' with h | h
  · left
    rw [hmx, h, hcen]
  · right
    rw [hmx, h, hcen, conjSub_map_apply]

end Lift

section HalfStable

open CFSG.LieType.BorelTits CFSG.QuasithinUnique.Borel252

variable {P H : Type} [Group P] [Group H] [Finite P] [Finite H]

omit [Finite P] [Finite H] in
theorem mem_normalizer_of_half {U R R' B₀ : Subgroup P} {s : P} (hH : L3Half U R R' B₀ s) :
    s ∈ Subgroup.normalizer (B₀ : Set P) := by
  have hs : s⁻¹ = s := inv_eq_of_mul_eq_one_right hH.s_sq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hH.s_norm x, fun hx => ?_⟩
  have := hH.s_norm _ hx
  rw [hs] at this
  have e : s * (s * x * s) * s = x := by
    calc s * (s * x * s) * s = (s * s) * x * (s * s) := by group
      _ = x := by rw [hH.s_sq]; group
  rwa [e] at this

omit [Finite P] in
theorem half_stable (Φ : P →* H) (hΦ : Function.Injective Φ) [Φ.range.Normal]
    {U R R' B₀ : Subgroup P} {s : P} (hSyl : IsSylowTwoOf (U.map Φ) ⊤)
    (hNUR : Subgroup.normalizer (U : Set P) ≤ Subgroup.normalizer (R : Set P))
    (hNUR' : Subgroup.normalizer (U : Set P) ≤ Subgroup.normalizer (R' : Set P))
    (hH : L3Half U R R' B₀ s) (hZne : ∃ x ∈ centerOf U, x ≠ 1)
    (hNM : Subgroup.normalizer ((U.map Φ : Subgroup H) : Set H) ≤
      Subgroup.normalizer ((R.map Φ : Subgroup H) : Set H))
    (hcentH : ∀ x ∈ centerOf (U.map Φ), x ≠ 1 → ∀ y ∈ Subgroup.normalizer ((R.map Φ : Subgroup H) :
      Set H), y * x = x * y → y ∈ Subgroup.normalizer ((U.map Φ : Subgroup H) : Set H))
    (hB₀N : B₀.map Φ ≤ Subgroup.normalizer ((U.map Φ : Subgroup H) : Set H)) {b : H}
    (hb : b ∈ Subgroup.normalizer ((U.map Φ : Subgroup H) : Set H) ⊓
      Subgroup.normalizer ((B₀.map Φ : Subgroup H) : Set H)) :
    (Φ s)⁻¹ * b * Φ s ∈ Subgroup.normalizer ((U.map Φ : Subgroup H) : Set H) ⊓
      Subgroup.normalizer ((B₀.map Φ : Subgroup H) : Set H) := by
  set T : Subgroup H := U.map Φ with hT
  set M : Subgroup H := Subgroup.normalizer ((R.map Φ : Subgroup H) : Set H) with hM
  have hUR : U ≤ Subgroup.normalizer (R : Set P) := Subgroup.le_normalizer.trans hNUR
  have hTM : T ≤ M := Subgroup.le_normalizer.trans hNM
  have hSylM : IsSylowTwoOf T M := F7.isSylowTwoOf_mono_right hSyl hTM le_top
  have hsM : Φ s ∈ M := map_mem_normalizer_map Φ hH.s_mem
  have hsN : Φ s ∉ Subgroup.normalizer (T : Set H) := by
    intro h
    have h1 : Φ s ∈ Subgroup.normalizer (T : Set H) ⊓ Φ.range := ⟨h, s, rfl⟩
    rw [hT, normalizer_map_inf_range Φ hΦ U] at h1
    obtain ⟨t, ht, hts⟩ := h1
    have : t = s := hΦ hts
    subst this
    exact hH.s_not (hNUR' ht)
  have hNT : ∀ X : Subgroup H, X ≤ Subgroup.normalizer (T : Set H) → IsPGroup 2 X → X ≤ T :=
    fun X hX hXp => le_of_le_normalizer_of_pgroup hSyl hX hXp
  have hZeq : centerOf T = (centerOf U).map Φ := centerOf_map_of_injective Φ hΦ U
  have hZneH : ∃ x ∈ centerOf T, x ≠ 1 := by
    obtain ⟨x, hx, hx1⟩ := hZne
    exact ⟨Φ x, by rw [hZeq]; exact Subgroup.mem_map_of_mem Φ hx,
      fun h => hx1 (hΦ (by rw [h, map_one]))⟩
  have hfixH := fix_transport Φ hΦ hSyl hUR hH.fix
  have hcases : ∀ T'' : Subgroup H, IsSylowTwoOf T'' M → B₀.map Φ ≤
      Subgroup.normalizer (T'' : Set H) → T'' = T ∨ T'' = conjSub (Φ s) T :=
    fun T'' hT'' hB => sylow_cases (T := T) (M := M) (N := Subgroup.normalizer (T : Set H))
      (Z := centerOf T) (B₀ := B₀.map Φ) (s := Φ s) hSylM hNT rfl hZneH hcentH hsM hfixH hT'' hB
  have hsB : Φ s ∈ Subgroup.normalizer ((B₀.map Φ : Subgroup H) : Set H) :=
    map_mem_normalizer_map Φ (mem_normalizer_of_half hH)
  have hs : s⁻¹ = s := inv_eq_of_mul_eq_one_right hH.s_sq
  exact star_stable (T := T) (B₀ := B₀.map Φ) (M := M) (s := Φ s) hNM hsM hsN hsB hB₀N hSylM
    hcases hb

end HalfStable

section MainLift

open CFSG.LieType.BorelTits CFSG.QuasithinUnique.Borel252

theorem exists_l3Datum_of_data {P H : Type} [Group P] [Group H] [Finite P] [Finite H]
    (Φ : P →* H) (hΦ : Function.Injective Φ) [Φ.range.Normal] (hodd : Odd Φ.range.index)
    {U R₁ R₂ B₀ : Subgroup P} {s₁ s₂ : P} (hD : L3DData U R₁ R₂ B₀ s₁ s₂)
    (N₁ N₂ : Subgroup H) (h₁ : N₁ = Subgroup.normalizer ((R₁.map Φ : Subgroup H) : Set H))
    (h₂ : N₂ = Subgroup.normalizer ((R₂.map Φ : Subgroup H) : Set H)) :
    Nonempty (L3Datum N₁ N₂) := by
  classical
  set T : Subgroup H := U.map Φ with hT
  set Q₁ : Subgroup H := R₁.map Φ with hQ₁
  set Q₂ : Subgroup H := R₂.map Φ with hQ₂
  set B₀' : Subgroup H := B₀.map Φ with hB₀'
  have hSyl : IsSylowTwoOf T ⊤ := isSylowTwoOf_map_of_odd Φ hΦ hodd hD.borel.sylow
  have hTp : IsPGroup 2 T := hSyl.2.1
  have hcenT : centerOf T = (centerOf U).map Φ := centerOf_map_of_injective Φ hΦ U
  have hUN₁ : U ≤ Subgroup.normalizer (R₁ : Set P) :=
    Subgroup.le_normalizer.trans hD.borel.lt₁.le
  have hUN₂ : U ≤ Subgroup.normalizer (R₂ : Set P) :=
    Subgroup.le_normalizer.trans hD.borel.lt₂.le
  have hTN₁ : T ≤ N₁ := by
    rintro _ ⟨u, hu, rfl⟩
    rw [h₁]; exact map_mem_normalizer_map Φ (hUN₁ hu)
  have hTN₂ : T ≤ N₂ := by
    rintro _ ⟨u, hu, rfl⟩
    rw [h₂]; exact map_mem_normalizer_map Φ (hUN₂ hu)
  have hF : Frame T Q₁ Q₂ := Frame.map Φ hΦ hD.frame
  have hSh : SpShape T ![Q₁, Q₂] := hF.toSpShape (h₁ ▸ hTN₁) (h₂ ▸ hTN₂)
  have hnormT : ∀ n ∈ Subgroup.normalizer (T : Set H), n ∈ N₁ ∧ n ∈ N₂ := fun n hn =>
    ⟨h₁ ▸ hSh.normalizer_le hSyl hn 0, h₂ ▸ hSh.normalizer_le hSyl hn 1⟩
  have hTsup : T = Q₁ ⊔ Q₂ := by rw [hT, hQ₁, hQ₂, ← Subgroup.map_sup, hD.borel.sup]
  have hNN : N₁ ⊓ N₂ = Subgroup.normalizer (T : Set H) := by
    apply le_antisymm
    · intro n hn
      rw [hTsup]
      exact mem_normalizer_sup (h₁ ▸ hn.1) (h₂ ▸ hn.2)
    · exact fun n hn => ⟨(hnormT n hn).1, (hnormT n hn).2⟩
  have hTle : T ≤ N₁ ⊓ N₂ := le_inf hTN₁ hTN₂
  have hS_eq : T = pCoreOf 2 (N₁ ⊓ N₂) := by
    apply le_antisymm
    · exact le_pCoreOf_of_le_normalizer 2 hTle hNN.le hTp
    · exact F7.isSylowTwoOf_pCoreOf_le (F7.isSylowTwoOf_mono_right hSyl hTle le_top)
  have hB₀N : B₀' ≤ Subgroup.normalizer (T : Set H) := by
    rintro _ ⟨b, hb, rfl⟩
    exact map_mem_normalizer_map Φ (hD.B₀_le hb)
  have hB₀I : B₀' ≤ Φ.range := Subgroup.map_le_range Φ B₀
  have hTI : T ≤ Φ.range := Subgroup.map_le_range Φ U
  have hodd₀ : Odd (Nat.card B₀') := by
    rw [hB₀', Subgroup.card_map_of_injective hΦ]; exact hD.B₀_odd
  have hTB : ∀ x ∈ T, x ∈ B₀' → x = 1 := fun x hx hxB => eq_one_of_pgroup_of_odd hTp hodd₀ hx hxB
  have hC : ∀ x ∈ T, (∀ b ∈ B₀', x * b = b * x) → x = 1 := by
    rintro _ ⟨u, hu, rfl⟩ hcomm
    have : u = 1 := hD.centS u hu (fun b hb => hΦ (by
      rw [map_mul, map_mul]; exact hcomm _ (Subgroup.mem_map_of_mem Φ hb)))
    rw [this, map_one]
  have hUp : IsPGroup 2 U := hD.borel.sylow.2.1
  have hcardP : Nat.card (Subgroup.normalizer (U : Set P)) = Nat.card U * Nat.card B₀ :=
    card_eq_mul_of_split Subgroup.le_normalizer hD.B₀_le
      (fun x hx hxB => eq_one_of_pgroup_of_odd hUp hD.B₀_odd hx hxB) hD.mul
  have hcard : Nat.card ↥(Subgroup.normalizer (T : Set H) ⊓ Φ.range) =
      Nat.card T * Nat.card B₀' := by
    rw [hT, normalizer_map_inf_range Φ hΦ U, Subgroup.card_map_of_injective hΦ, hcardP,
      Subgroup.card_map_of_injective hΦ, hB₀', Subgroup.card_map_of_injective hΦ]
  have hcop : Nat.Coprime (Nat.card T) (Nat.card B₀') := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hTp
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd₀)
  have hmul : ∀ n ∈ Subgroup.normalizer (T : Set H), ∃ t ∈ T,
      ∃ b ∈ Subgroup.normalizer (T : Set H) ⊓ Subgroup.normalizer (B₀' : Set H), n = t * b :=
    fun n hn => star_mul hTI hB₀I hB₀N hcard hcop hn
  have hBsodd := star_odd hSyl hB₀N hTB hC hmul
  have hB₀Bs : B₀' ≤ Subgroup.normalizer (T : Set H) ⊓ Subgroup.normalizer (B₀' : Set H) :=
    le_inf hB₀N Subgroup.le_normalizer
  have hcentH : ∀ x ∈ centerOf T, x ≠ 1 →
      Subgroup.centralizer ({x} : Set H) ≤ Subgroup.normalizer (T : Set H) := by
    intro x hx hx1
    rw [hcenT] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    have hx1' : x' ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hUC : U ≤ Subgroup.centralizer ({x'} : Set P) := fun u hu => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mem_centerOf_iff.mp hx').2 u hu
    have hcP : pCoreOf 2 (Subgroup.centralizer ({x'} : Set P)) = U := by
      apply le_antisymm
      · exact F7.isSylowTwoOf_pCoreOf_le (F7.isSylowTwoOf_mono_right hD.borel.sylow hUC le_top)
      · exact le_pCoreOf_of_le_normalizer 2 hUC (hD.cent x' hx' hx1') hUp
    exact centralizer_le_normalizer_of_pCoreOf Φ hΦ x' hcP
  have hZne : ∃ x ∈ centerOf U, x ≠ 1 := by
    obtain ⟨x, hx, -, -, hx1, -, -⟩ := hD.Z_big
    exact ⟨x, hx, hx1⟩
  have hNM₁ : Subgroup.normalizer (T : Set H) ≤ N₁ := fun n hn => (hnormT n hn).1
  have hNM₂ : Subgroup.normalizer (T : Set H) ≤ N₂ := fun n hn => (hnormT n hn).2
  have hstab₁ := fun {b : H} (hb : b ∈ Subgroup.normalizer (T : Set H) ⊓
      Subgroup.normalizer (B₀' : Set H)) =>
    half_stable Φ hΦ hSyl hD.borel.lt₁.le hD.borel.lt₂.le hD.half₁ hZne (h₁ ▸ hNM₁)
      (fun x hx hx1 y hy hyx => hcentH x hx hx1 (Subgroup.mem_centralizer_singleton_iff.mpr hyx))
      hB₀N hb
  have hstab₂ := fun {b : H} (hb : b ∈ Subgroup.normalizer (T : Set H) ⊓
      Subgroup.normalizer (B₀' : Set H)) =>
    half_stable Φ hΦ hSyl hD.borel.lt₂.le hD.borel.lt₁.le hD.half₂ hZne (h₂ ▸ hNM₂)
      (fun x hx hx1 y hy hyx => hcentH x hx hx1 (Subgroup.mem_centralizer_singleton_iff.mpr hyx))
      hB₀N hb
  have hinv₁ : (Φ s₁)⁻¹ = Φ s₁ := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right hD.half₁.s_sq]
  have hinv₂ : (Φ s₂)⁻¹ = Φ s₂ := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right hD.half₂.s_sq]
  have hfix₁ := fix_transport Φ hΦ hSyl hUN₁ hD.half₁.fix
  have hfix₂ := fix_transport Φ hΦ hSyl hUN₂ hD.half₂.fix
  have hcov : ∀ (R : Subgroup P) (N' : Subgroup H), N' = Subgroup.normalizer
      ((R.map Φ : Subgroup H) : Set H) →
      (∀ x ∈ R, x ≠ 1 → ∃ m ∈ Subgroup.normalizer (R : Set P), m * x * m⁻¹ ∈ centerOf U) →
      ∀ x ∈ R.map Φ, x ≠ 1 → ∃ m ∈ N', m * x * m⁻¹ ∈ centerOf T := by
    intro R N' hN' hcv x hx hx1
    obtain ⟨x', hx', rfl⟩ := hx
    have hx1' : x' ≠ 1 := fun h => hx1 (by rw [h, map_one])
    obtain ⟨m, hm, hmx⟩ := hcv x' hx' hx1'
    refine ⟨Φ m, by rw [hN']; exact map_mem_normalizer_map Φ hm, ?_⟩
    rw [hcenT, ← map_mul, ← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem Φ hmx
  have hnonsolv : ∀ (R : Subgroup P) (N' : Subgroup H), N' = Subgroup.normalizer
      ((R.map Φ : Subgroup H) : Set H) → ¬ Group.IsSolvable ↥(Subgroup.normalizer (R : Set P)) →
      ¬ Group.IsSolvable ↥N' := by
    intro R N' hN' hns hsolv
    apply hns
    let f : ↥(Subgroup.normalizer (R : Set P)) →* ↥N' :=
      (Φ.comp (Subgroup.normalizer (R : Set P)).subtype).codRestrict N'
        (fun x => by rw [hN']; exact map_mem_normalizer_map Φ x.2)
    exact Group.isSolvable_of_isSolvable_injective (f := f) (fun a b hab => Subtype.ext
      (hΦ (congrArg Subtype.val hab)))
  have hnot : ∀ (R' : Subgroup P) (N'' : Subgroup H) (s : P), N'' = Subgroup.normalizer
      ((R'.map Φ : Subgroup H) : Set H) → s ∉ Subgroup.normalizer (R' : Set P) → Φ s ∉ N'' := by
    intro R' N'' s hN'' hs h
    rw [hN''] at h
    have h1 : Φ s ∈ Subgroup.normalizer ((R'.map Φ : Subgroup H) : Set H) ⊓ Φ.range := ⟨h, s, rfl⟩
    rw [normalizer_map_inf_range Φ hΦ R'] at h1
    obtain ⟨t, ht, hts⟩ := h1
    have : t = s := hΦ hts
    subst this
    exact hs ht
  exact ⟨{
    S := T
    B := Subgroup.normalizer (T : Set H) ⊓ Subgroup.normalizer (B₀' : Set H)
    Q₁ := Q₁
    Q₂ := Q₂
    s₁ := Φ s₁
    s₂ := Φ s₂
    S_eq := hS_eq
    B_le := hNN ▸ inf_le_left
    B_odd := hBsodd
    mul_SB := fun h hh => hmul h (hNN ▸ hh)
    S_index := F7.isSylowTwoOf_odd_relIndex (F7.isSylowTwoOf_mono_right hSyl hTN₁ le_top)
    frame := hF
    Q₁_norm := fun m hm x hx => (Subgroup.mem_normalizer_iff.mp (h₁ ▸ hm) x).mp hx
    Q₂_norm := fun m hm x hx => (Subgroup.mem_normalizer_iff.mp (h₂ ▸ hm) x).mp hx
    trans := by
      intro x hx hx1 y hy hy1
      rw [hcenT] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      have hx1' : x' ≠ 1 := fun h => hx1 (by rw [h, map_one])
      have hy1' : y' ≠ 1 := fun h => hy1 (by rw [h, map_one])
      obtain ⟨b, hb, hbxy⟩ := hD.trans x' hx' hx1' y' hy' hy1'
      exact ⟨Φ b, hB₀Bs (Subgroup.mem_map_of_mem Φ hb), by
        rw [← map_mul, ← map_inv, ← map_mul, hbxy]⟩
    cent := fun x hx hx1 y _ hy =>
      (hnormT y (hcentH x hx hx1 (Subgroup.mem_centralizer_singleton_iff.mpr hy))).2
    cov₁ := hcov R₁ N₁ h₁ hD.half₁.cov
    cov₂ := hcov R₂ N₂ h₂ hD.half₂.cov
    nonsolv := hnonsolv R₁ N₁ h₁ hD.half₁.nonsolv
    s₁_mem := by rw [h₁]; exact map_mem_normalizer_map Φ hD.half₁.s_mem
    s₁_not := hnot R₂ N₂ s₁ h₂ hD.half₁.s_not
    s₁_sq := by rw [← map_mul, hD.half₁.s_sq, map_one]
    s₁_norm := fun b hb => by
      have e : Φ s₁ * b * (Φ s₁)⁻¹ = (Φ s₁)⁻¹ * b * Φ s₁ := by rw [hinv₁]
      rw [e]
      exact hstab₁ hb
    s₂_mem := by rw [h₂]; exact map_mem_normalizer_map Φ hD.half₂.s_mem
    s₂_not := hnot R₁ N₁ s₂ h₁ hD.half₂.s_not
    s₂_sq := by rw [← map_mul, hD.half₂.s_sq, map_one]
    s₂_norm := fun b hb => by
      have e : Φ s₂ * b * (Φ s₂)⁻¹ = (Φ s₂)⁻¹ * b * Φ s₂ := by rw [hinv₂]
      rw [e]
      exact hstab₂ hb
    fix₁ := fun m hm hN => hfix₁ m (h₁ ▸ hm) (fun c hc z hz => hN c (hB₀Bs hc) z hz)
    fix₂ := fun m hm hN => hfix₂ m (h₂ ▸ hm) (fun c hc z hz => hN c (hB₀Bs hc) z hz)
    centS := fun x hx hcomm => hC x hx (fun b hb => hcomm b (hB₀Bs hb))
    Z_big := by
      obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ := hD.Z_big
      refine ⟨Φ x, by rw [hcenT]; exact Subgroup.mem_map_of_mem Φ hx, Φ y,
        by rw [hcenT]; exact Subgroup.mem_map_of_mem Φ hy, ?_, ?_, ?_⟩
      · exact fun h => hx1 (hΦ (by rw [h, map_one]))
      · exact fun h => hy1 (hΦ (by rw [h, map_one]))
      · exact fun h => hxy (hΦ h)
    rot := by
      have hrot : (Φ s₁ * Φ s₂) ^ 3 = 1 := by rw [← map_mul, ← map_pow, hD.rot, map_one]
      refine ⟨1, Subgroup.one_mem _, fun x _ => ?_⟩
      simp [hrot] }⟩

end MainLift

end CFSG.Quasithin.H13.F431.L3
