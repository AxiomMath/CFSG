module

public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.VolIC113
public import CFSG.Quasithin.Vol2.Ch4Sec3C64Coord

public section

namespace CFSG.Quasithin.H13.Ch4.C64

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA x, hB x]

theorem mem_normalizer_of_conj_mem {S : Subgroup G} {g : G} (h : ∀ x ∈ S, g * x * g⁻¹ ∈ S) :
    g ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : S.map (MulAut.conj g).toMonoidHom ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem exists_mem_of_lt {W R X : Subgroup G} (hW : IsPGroup 2 W) (hRX : R < X) (hXW : X ≤ W)
    (hRn : W ≤ Subgroup.normalizer (R : Set G)) (hXn : W ≤ Subgroup.normalizer (X : Set G)) :
    ∃ y ∈ X, y ∉ R ∧ y ^ 2 ∈ R ∧ ∀ w ∈ W, w * y * w⁻¹ * y⁻¹ ∈ R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥W := R.subgroupOf W with hNdef
  have hN : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hRn
  have hQ : IsPGroup 2 (↥W ⧸ N) := hW.to_quotient N
  have : Group.IsNilpotent (↥W ⧸ N) := hQ.isNilpotent
  set M : Subgroup (↥W ⧸ N) := (X.subgroupOf W).map (QuotientGroup.mk' N) with hMdef
  have hXN : (X.subgroupOf W).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXn
  have hMn : M.Normal := hXN.map _ (QuotientGroup.mk'_surjective N)
  have hMne : M ≠ ⊥ := by
    obtain ⟨x, hxX, hxR⟩ := IsConcreteLE.exists_of_lt hRX
    intro hM
    have h1 : QuotientGroup.mk' N ⟨x, hXW hxX⟩ ∈ M := ⟨⟨x, hXW hxX⟩, hxX, rfl⟩
    rw [hM, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hxR h1
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hMne
  have hZ2 : IsPGroup 2 ↥(M ⊓ Subgroup.center (↥W ⧸ N)) := hQ.to_subgroup _
  have hdvd : 2 ∣ Nat.card ↥(M ⊓ Subgroup.center (↥W ⧸ N)) := by
    obtain ⟨n, hn⟩ := hZ2.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hZ
      rw [Subgroup.eq_bot_iff_card, hn, pow_zero]
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  obtain ⟨⟨x, hxW⟩, hxX, hxz⟩ := z.2.1
  have hzc := z.2.2
  refine ⟨x, hxX, ?_, ?_, ?_⟩
  · intro hxR
    have h1 : (z : ↥W ⧸ N) = 1 := by
      rw [← hxz, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hxR
    have h2 : z = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · have h1 : ((z : ↥W ⧸ N)) ^ 2 = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz] at this
      exact congrArg Subtype.val this
    rw [← hxz, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  · intro w hw
    have h1 := Subgroup.mem_center_iff.1 hzc (QuotientGroup.mk' N ⟨w, hw⟩)
    rw [← hxz, ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    have h2 : ((⟨w, hw⟩ * ⟨x, hxW⟩ : ↥W)⁻¹ * (⟨x, hxW⟩ * ⟨w, hw⟩) : ↥W) ∈ N := h1
    rw [hNdef, Subgroup.mem_subgroupOf] at h2
    have h3 : w * x * w⁻¹ * x⁻¹ =
        (w * x) * ((w * x)⁻¹ * (x * w))⁻¹ * (w * x)⁻¹ := by group
    rw [h3]
    exact (Subgroup.mem_normalizer_iff.1 (hRn (W.mul_mem hw hxW)) _).1 (R.inv_mem (by
      simpa using h2))

structure Hyp64 (L R TH Sig : Subgroup G) (α : ↥L →* alternatingGroup (Fin 7))
    (β : ↥(blockU L) →* Multiplicative (AltHeart 7)) (a b : Fin 7) : Prop where
  blk : A7Blk L α β
  hab : a ≠ b
  RN : R ≤ Subgroup.normalizer (L : Set G)
  TH2 : IsPGroup 2 TH
  RTH : R ≤ TH
  THR : TH ≤ Subgroup.normalizer (R : Set G)
  THS : TH ≤ Subgroup.normalizer (Sig : Set G)
  C623 : ∀ R₀ : Subgroup G, R₀ ≠ ⊥ → R₀ ≤ R → L ⊔ TH ≤ Subgroup.normalizer (R₀ : Set G) →
    ¬ Sig ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (R₀ : Set G)
  THL : TH ≤ Subgroup.normalizer (L : Set G)
  R1 : ∀ r : ↥(Subgroup.normalizer (L : Set G)), (r : G) ∈ R →
    (∀ k : ↥L, α ((conjAct L r) k) = α k) ∨
      ∀ k : ↥L, ((α ((conjAct L r) k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
        swap a b * (α k : Perm (Fin 7)) * (swap a b)⁻¹
  R2 : ∃ r : ↥(Subgroup.normalizer (L : Set G)), (r : G) ∈ R ∧
    ∀ k : ↥L, ((α ((conjAct L r) k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      swap a b * (α k : Perm (Fin 7)) * (swap a b)⁻¹
  QR : pCoreOf 2 (L ⊔ TH) ≤ R
  R4 : ∀ r ∈ R, (∀ l ∈ L, l * r * l⁻¹ * r⁻¹ ∈ pCoreOf 2 L) → r ∈ pCoreOf 2 (L ⊔ TH)
  II : ∀ R₀ : Subgroup G, R₀ ≠ ⊥ → R₀ ≤ R → L ⊔ TH ≤ Subgroup.normalizer (R₀ : Set G) →
    Sig ⊓ Subgroup.normalizer (R₀ : Set G) = R
  Sig2 : IsPGroup 2 Sig

namespace Hyp64

variable {L R TH Sig : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)}
  {β : ↥(blockU L) →* Multiplicative (AltHeart 7)} {a b : Fin 7}
  (h : Hyp64 L R TH Sig α β a b)
include h

theorem U_le_Q : blockU L ≤ pCoreOf 2 (L ⊔ TH) :=
  VolI.blockU_le_pCoreOf h.blk.short h.THL

omit [Finite G] in
theorem U_ne_bot : blockU L ≠ ⊥ := by
  intro hU
  have h1 := h.blk.short.2.2.2.2.1
  rw [hU] at h1
  exact (not_lt_bot h1)

theorem H_le_N_U : L ⊔ TH ≤ Subgroup.normalizer (blockU L : Set G) :=
  sup_le (C1.le_normalizer_blockU L) fun _ ht => C1.mem_normalizer_blockU (h.THL ht)

theorem R_le_N_U : R ≤ Subgroup.normalizer (blockU L : Set G) :=
  fun _ hr => h.H_le_N_U (Subgroup.mem_sup_right (h.RTH hr))

theorem Q_ne_bot : pCoreOf 2 (L ⊔ TH) ≠ ⊥ := fun hQ =>
  h.U_ne_bot (eq_bot_iff.2 (hQ ▸ h.U_le_Q))

theorem R_le_Sig : R ≤ Sig := by
  have h1 := h.II _ h.Q_ne_bot h.QR
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (L ⊔ TH))
  rw [← h1]
  exact inf_le_left

theorem exists_y :
    ∃ y ∈ Sig ⊓ Subgroup.normalizer (R : Set G), y ∉ R ∧ y ^ 2 ∈ R ∧
      (∀ t ∈ TH, t * y * t⁻¹ * y⁻¹ ∈ R) ∧
      ∃ u ∈ blockU L, y * u * y⁻¹ ∉ pCoreOf 2 (L ⊔ TH) := by
  classical
  have hL := h.blk.short
  set Q := pCoreOf 2 (L ⊔ TH) with hQ
  set X := Sig ⊓ Subgroup.normalizer (R : Set G) with hX
  have hRX : R < X := by
    refine lt_of_le_of_ne (le_inf h.R_le_Sig Subgroup.le_normalizer) fun hRX => ?_
    apply h.C623 (blockU L) h.U_ne_bot (h.U_le_Q.trans h.QR) h.H_le_N_U
    rw [← hX, ← hRX]
    exact h.R_le_N_U
  have hW : IsPGroup 2 ↥(X ⊔ TH) := by
    have h1 : IsPGroup 2 ↥(TH ⊔ Sig) := IsPGroup.to_sup_of_normal_right' h.TH2 h.Sig2 h.THS
    exact h1.to_le (sup_le (inf_le_left.trans le_sup_right) le_sup_left)
  have hRn : X ⊔ TH ≤ Subgroup.normalizer (R : Set G) := sup_le inf_le_right h.THR
  have hXn : X ⊔ TH ≤ Subgroup.normalizer (X : Set G) := by
    refine sup_le Subgroup.le_normalizer fun t ht => ?_
    exact mem_normalizer_inf (h.THS ht) (Subgroup.le_normalizer (h.THR ht))
  obtain ⟨y, hyX, hyR, hy2, hyc⟩ := exists_mem_of_lt hW hRX le_sup_left hRn hXn
  refine ⟨y, hyX, hyR, hy2, fun t ht => hyc t (Subgroup.mem_sup_right ht), ?_⟩
  by_contra hcon
  push Not at hcon
  have hyN : y ∈ Subgroup.normalizer (R : Set G) := hyX.2
  set Uy := (blockU L).map (MulAut.conj y).toMonoidHom with hUy
  set U₀ := blockU L ⊔ Uy with hU₀
  have hUyQ : Uy ≤ Q := by
    rintro _ ⟨u, hu, rfl⟩
    exact hcon u hu
  have hU₀Q : U₀ ≤ Q := sup_le h.U_le_Q hUyQ
  have hU₀ne : U₀ ≠ ⊥ := fun h0 => h.U_ne_bot (eq_bot_iff.2 (h0 ▸ le_sup_left))
  have hLU₀ : L ≤ Subgroup.normalizer (U₀ : Set G) := by
    intro l hl
    apply mem_normalizer_of_conj_mem
    intro x hx
    have h1 : x * l * x⁻¹ * l⁻¹ ∈ blockU L := VolI.commutator_mem_blockU hL h.THL (hU₀Q hx) hl
    have h2 : l * x * l⁻¹ = (x * l * x⁻¹ * l⁻¹)⁻¹ * x := by group
    rw [h2]
    exact U₀.mul_mem (U₀.inv_mem (Subgroup.mem_sup_left h1)) hx
  have hTU₀ : TH ≤ Subgroup.normalizer (U₀ : Set G) := by
    intro t ht
    apply mem_normalizer_of_conj_mem
    have htU : t ∈ Subgroup.normalizer (blockU L : Set G) := C1.mem_normalizer_blockU (h.THL ht)
    have hUyt : ∀ x ∈ Uy, t * x * t⁻¹ ∈ Uy := by
      rintro _ ⟨u, hu, rfl⟩
      have hrR : t * y * t⁻¹ * y⁻¹ ∈ R := hyc t (Subgroup.mem_sup_right ht)
      have hr' : y⁻¹ * (t * y * t⁻¹ * y⁻¹) * y ∈ R := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hyN) _).1 hrR
        simpa using this
      have hu' : t * u * t⁻¹ ∈ blockU L := (Subgroup.mem_normalizer_iff.1 htU u).1 hu
      have hu'' := (Subgroup.mem_normalizer_iff.1 (h.R_le_N_U hr') _).1 hu'
      refine ⟨_, hu'', ?_⟩
      show y * ((y⁻¹ * (t * y * t⁻¹ * y⁻¹) * y) * (t * u * t⁻¹) *
        (y⁻¹ * (t * y * t⁻¹ * y⁻¹) * y)⁻¹) * y⁻¹ = t * (y * u * y⁻¹) * t⁻¹
      group
    have hle : U₀ ≤ U₀.comap (MulAut.conj t).toMonoidHom := by
      refine sup_le (fun u hu => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 htU u).1 hu)
      · exact Subgroup.mem_sup_right (hUyt x hx)
    intro x hx
    exact hle hx
  have hyU₀ : y ∈ Subgroup.normalizer (U₀ : Set G) := by
    apply mem_normalizer_of_conj_mem
    have hle : U₀ ≤ U₀.comap (MulAut.conj y).toMonoidHom := by
      refine sup_le (fun u hu => Subgroup.mem_sup_right ⟨u, hu, rfl⟩) ?_
      rintro _ ⟨u, hu, rfl⟩
      apply Subgroup.mem_sup_left
      have h1 := (Subgroup.mem_normalizer_iff.1 (h.R_le_N_U hy2) u).1 hu
      show y * (y * u * y⁻¹) * y⁻¹ ∈ blockU L
      have e : y * (y * u * y⁻¹) * y⁻¹ = y ^ 2 * u * (y ^ 2)⁻¹ := by
        rw [pow_two]
        group
      rw [e]
      exact h1
    intro x hx
    exact hle hx
  have hII := h.II U₀ hU₀ne (hU₀Q.trans h.QR) (sup_le hLU₀ hTU₀)
  have hyR' : y ∈ Sig ⊓ Subgroup.normalizer (U₀ : Set G) := ⟨hyX.1, hyU₀⟩
  rw [hII] at hyR'
  exact hyR hyR'

end Hyp64

end CFSG.Quasithin.H13.Ch4.C64
