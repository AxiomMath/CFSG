module

public import CFSG.Quasithin.Background.B2FactorizationBlocks
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace A6Tv

variable {V : Type*} [CommGroup V]

theorem card_sup_mul_card_inf (A B : Subgroup V) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have : B.Normal := Subgroup.normal_of_isMulCommutative B
  have h1 := Subgroup.relIndex_mul_card (H := B) (K := A ⊔ B)
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : B ≤ A ⊔ B)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem eq_top_of_invariant {X : Subgroup (MulAut V)} {W Y : Subgroup V}
    (hgen : (⨆ m ∈ X, W.map (m : MulAut V).toMonoidHom) = ⊤) (hWY : W ≤ Y)
    (hY : ∀ x ∈ X, ∀ y ∈ Y, x y ∈ Y) : Y = ⊤ := by
  rw [eq_top_iff, ← hgen]
  refine iSup₂_le fun m hm => ?_
  rintro _ ⟨w, hw, rfl⟩
  exact hY m hm w (hWY hw)

theorem inf_eq_bot_or_le [Finite V] {W Y : Subgroup V} (hW : Nat.card W = 4) {c : MulAut V}
    (hcW : ∀ w ∈ W, c w ∈ W) (hfix : ∀ w ∈ W, c w = w → w = 1)
    (hcY : ∀ y ∈ Y, c y ∈ Y) : W ⊓ Y = ⊥ ∨ W ≤ Y := by
  classical
  by_cases hb : W ⊓ Y = ⊥
  · exact Or.inl hb
  right
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hb
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hcy : c y ∈ W ⊓ Y := ⟨hcW y hy.1, hcY y hy.2⟩
  have hcy1 : c y ≠ 1 := fun h => hy1' (c.injective (by rw [h, map_one]))
  have hcyy : c y ≠ y := fun h => hy1' (hfix y hy.1 h)
  have h3 : ({1, y, c y} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hcyy.symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hy1'.symm, hcy1.symm⟩
  have hle : ({1, y, c y} : Finset V).card ≤ Nat.card ↥(W ⊓ Y) := by
    refine B1.card_le_of_finset_subset _ fun f hf => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl
    · exact (W ⊓ Y).one_mem
    · exact hy
    · exact hcy
  have hdvd : Nat.card ↥(W ⊓ Y) ∣ 4 := hW ▸ Subgroup.card_dvd_of_le inf_le_left
  have h4 : Nat.card ↥(W ⊓ Y) = 4 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card ↥(W ⊓ Y) <;> omega
  have heq : W ⊓ Y = W := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, hW])
  exact heq ▸ inf_le_right

theorem conjAut_inj {g : MulAut V} {A B : Subgroup (MulAut V)}
    (h : B1.conjAut g A = B1.conjAut g B) : A = B := by
  rw [← B1.conjAut_inv_conjAut g A, h, B1.conjAut_inv_conjAut]

theorem conjAut_mul' (a b : MulAut V) (K : Subgroup (MulAut V)) :
    B1.conjAut (a * b) K = B1.conjAut a (B1.conjAut b K) := by
  ext x
  simp only [B1.mem_conjAut, mul_inv_rev, mul_assoc]

theorem conjAut_eq_iff {x : MulAut V} {B : Subgroup (MulAut V)} :
    B1.conjAut x B = B ↔ x ∈ Subgroup.normalizer (B : Set (MulAut V)) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hx h
    constructor
    · intro hh
      rw [← hx, B1.mem_conjAut]
      simpa [mul_assoc] using hh
    · intro hh
      rw [← hx, B1.mem_conjAut] at hh
      simpa [mul_assoc] using hh
  · intro hx
    ext y
    rw [B1.mem_conjAut, hx (x⁻¹ * y * x)]
    simp [mul_assoc]

theorem mem_commSub_of_conjAut {B : Subgroup (MulAut V)} {c : MulAut V}
    (hcB : B1.conjAut c B = B) {u : V} (hu : u ∈ commSub (⊤ : Subgroup V) B) :
    c u ∈ commSub (⊤ : Subgroup V) B := by
  rw [← hcB, ← IsTransvectionBlocks.map_commSub_conjAut]
  exact Subgroup.mem_map_of_mem _ hu

variable {J : Subgroup (MulAut V)} {𝓗 : Finset (Subgroup (MulAut V))}

theorem exists_inner [Finite V] (hb : IsTransvectionBlocks J 𝓗) {B : Subgroup (MulAut V)}
    (hB : B ∈ 𝓗) {c : MulAut V} (hcB : B1.conjAut c B = B) {n : ℕ} (hcn : c ^ 3 ^ n = 1) :
    ∃ k ∈ B, k ^ 3 = 1 ∧ ∀ v ∈ commSub (⊤ : Subgroup V) B, c v = k v := by
  set U := commSub (⊤ : Subgroup V) B with hU
  have hcU : c ∈ stabSub U := by
    intro u
    have hmap := IsTransvectionBlocks.map_commSub_conjAut B c
    rw [hcB] at hmap
    constructor
    · intro hu
      rw [hU, ← hmap] at hu
      obtain ⟨u', hu', he⟩ := Subgroup.mem_map.1 hu
      have : u' = u := c.injective he
      exact this ▸ hu'
    · intro hu
      exact mem_commSub_of_conjAut hcB hu
  have hmem : resHom U ⟨c, hcU⟩ ∈ autSub B U := by
    rw [hb.autSub_eq_top B hB]
    trivial
  obtain ⟨g, hgB, hg⟩ := mem_autSub.1 hmem
  have hgc : ∀ v ∈ U, (g : MulAut V) v = c v := fun v hv => by
    have := congrArg (fun φ : MulAut ↥U => ((φ ⟨v, hv⟩ : ↥U) : V)) hg
    simpa [resHom_apply] using this
  refine ⟨g, hgB, ?_, fun v hv => (hgc v hv).symm⟩
  have h2 : resHom U (g ^ 3 ^ n) = 1 := by
    rw [map_pow, hg, ← map_pow]
    have : (⟨c, hcU⟩ : ↥(stabSub U)) ^ 3 ^ n = 1 := Subtype.ext (by simpa using hcn)
    rw [this, map_one]
  have h3 : (g : MulAut V) ^ 3 ^ n ∈ B ⊓ centSub U := by
    refine ⟨B.pow_mem hgB _, fun u hu => ?_⟩
    have := congrArg (fun φ : MulAut ↥U => ((φ ⟨u, hu⟩ : ↥U) : V)) h2
    have e1 : ((resHom U (g ^ 3 ^ n) ⟨u, hu⟩ : ↥U) : V) = ((g : MulAut V) ^ 3 ^ n) u := by
      rw [resHom_apply]
      rfl
    exact e1.symm.trans (this.trans rfl)
  rw [hb.inf_centSub hB, Subgroup.mem_bot] at h3
  have h6 : orderOf (g : MulAut V) ∣ 3 * 2 := by
    have := Subgroup.orderOf_dvd_natCard B hgB
    rwa [hb.card_eq B hB] at this
  have hco : Nat.Coprime (orderOf (g : MulAut V)) 2 :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h3)
      (Nat.Coprime.pow_left n (by norm_num))
  exact orderOf_dvd_iff_pow_eq_one.1 (hco.dvd_of_dvd_mul_right h6)

theorem conj_eq_of_inner [Finite V] (hb : IsTransvectionBlocks J 𝓗)
    {B : Subgroup (MulAut V)} (hB : B ∈ 𝓗) {c k : MulAut V} (hcB : B1.conjAut c B = B)
    (hkB : k ∈ B) (hck : ∀ v ∈ commSub (⊤ : Subgroup V) B, c v = k v) {b : MulAut V}
    (hbB : b ∈ B) : c * b * c⁻¹ = k * b * k⁻¹ := by
  have h1 : c * b * c⁻¹ ∈ B := by
    rw [← hcB, B1.mem_conjAut]
    simpa [mul_assoc] using hbB
  have h2 : k * b * k⁻¹ ∈ B := B.mul_mem (B.mul_mem hkB hbB) (B.inv_mem hkB)
  have h3 : (k * b * k⁻¹)⁻¹ * (c * b * c⁻¹) ∈ B ⊓ centSub (commSub (⊤ : Subgroup V) B) := by
    refine ⟨B.mul_mem (B.inv_mem h2) h1, fun u hu => ?_⟩
    have hku : k⁻¹ u ∈ commSub (⊤ : Subgroup V) B := hb.stab B hB _ (B.inv_mem hkB) u hu
    have hci : c⁻¹ u = k⁻¹ u := by
      have h1 : c (k⁻¹ u) = u := by rw [hck _ hku, MulAut.apply_inv_self V k u]
      calc c⁻¹ u = c⁻¹ (c (k⁻¹ u)) := by rw [h1]
        _ = k⁻¹ u := MulAut.inv_apply_self V c _
    have hbu : b (k⁻¹ u) ∈ commSub (⊤ : Subgroup V) B := hb.stab B hB _ hbB _ hku
    show ((k * b * k⁻¹)⁻¹ * (c * b * c⁻¹)) u = u
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hci, hck _ hbu]
    show (k * b * k⁻¹)⁻¹ ((k * b * k⁻¹) u) = u
    exact MulAut.inv_apply_self V _ u
  rw [hb.inf_centSub hB, Subgroup.mem_bot, inv_mul_eq_one] at h3
  exact h3.symm

theorem absorb [Finite V] (hb : IsTransvectionBlocks J 𝓗)
    {B : Subgroup (MulAut V)} (hB : B ∈ 𝓗) {c k k' : MulAut V} (hcB : B1.conjAut c B = B)
    (hkB : k ∈ B) (hck : ∀ v ∈ commSub (⊤ : Subgroup V) B, c v = k v)
    (hk'b : ∀ b ∈ B, k' * b = b * k') (hk'u : ∀ u ∈ commSub (⊤ : Subgroup V) B, k' u = u) :
    (∀ b ∈ B, (k * k')⁻¹ * c * b = b * ((k * k')⁻¹ * c)) ∧
      ∀ u ∈ commSub (⊤ : Subgroup V) B, ((k * k')⁻¹ * c) u = u := by
  refine ⟨fun b hbB => ?_, fun u hu => ?_⟩
  · have hcb : c * b = k * b * k⁻¹ * c := by
      rw [← conj_eq_of_inner hb hB hcB hkB hck hbB]
      group
    have hkb : k'⁻¹ * b = b * k'⁻¹ := by
      have := hk'b b hbB
      calc k'⁻¹ * b = k'⁻¹ * (b * k') * k'⁻¹ := by group
        _ = k'⁻¹ * (k' * b) * k'⁻¹ := by rw [this]
        _ = b * k'⁻¹ := by group
    calc (k * k')⁻¹ * c * b = k'⁻¹ * k⁻¹ * (c * b) := by group
      _ = k'⁻¹ * k⁻¹ * (k * b * k⁻¹ * c) := by rw [hcb]
      _ = (k'⁻¹ * b) * k⁻¹ * c := by group
      _ = (b * k'⁻¹) * k⁻¹ * c := by rw [hkb]
      _ = b * ((k * k')⁻¹ * c) := by group
  · have hk'i : k'⁻¹ u = u := by
      calc k'⁻¹ u = k'⁻¹ (k' u) := by rw [hk'u u hu]
        _ = u := MulAut.inv_apply_self V _ _
    rw [mul_inv_rev, MulAut.mul_apply, MulAut.mul_apply, hck u hu]
    show k'⁻¹ (k⁻¹ (k u)) = u
    rw [MulAut.inv_apply_self V k u]
    exact hk'i

theorem three_le_pRank {G : Type*} [Group G] [Finite G] {X : Subgroup G} {a b w : G}
    (ha : a ∈ X) (hb : b ∈ X) (hw : w ∈ X) (hab : Commute a b) (haw : Commute a w)
    (hbw : Commute b w) (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) (hw3 : orderOf w = 3)
    (hi : ∀ i j k : ℤ, a ^ i * b ^ j * w ^ k = 1 → a ^ i = 1 ∧ b ^ j = 1) :
    3 ≤ CFSG.Open.pRank 3 X := by
  have hcomm₁ : ∀ (y : ↥(Subgroup.zpowers b)) (z : ↥(Subgroup.zpowers w)),
      Commute ((Subgroup.zpowers b).subtype y) ((Subgroup.zpowers w).subtype z) := by
    rintro ⟨y, hy⟩ ⟨z, hz⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact hbw.zpow_zpow j k
  let f₁ := MonoidHom.noncommCoprod (Subgroup.zpowers b).subtype (Subgroup.zpowers w).subtype
    hcomm₁
  have hcomm₂ : ∀ (x : ↥(Subgroup.zpowers a))
      (yz : ↥(Subgroup.zpowers b) × ↥(Subgroup.zpowers w)),
      Commute ((Subgroup.zpowers a).subtype x) (f₁ yz) := by
    rintro ⟨x, hx⟩ ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    show Commute (a ^ i) (b ^ j * w ^ k)
    exact (hab.zpow_zpow i j).mul_right (haw.zpow_zpow i k)
  let f := MonoidHom.noncommCoprod (Subgroup.zpowers a).subtype f₁ hcomm₂
  have hfapp : ∀ (x : ↥(Subgroup.zpowers a)) (y : ↥(Subgroup.zpowers b))
      (z : ↥(Subgroup.zpowers w)), f (x, (y, z)) = (x : G) * ((y : G) * z) :=
    fun _ _ _ => rfl
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨⟨x, hx⟩, ⟨⟨y, hy⟩, ⟨z, hz⟩⟩⟩ h
    have h1 : x * (y * z) = 1 := h
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← mul_assoc] at h1
    obtain ⟨hi1, hj1⟩ := hi i j k h1
    have hk1 : w ^ k = 1 := by rw [hi1, hj1, one_mul, one_mul] at h1; exact h1
    rw [Subgroup.mem_bot]
    refine Prod.ext (Subtype.ext hi1) (Prod.ext (Subtype.ext hj1) (Subtype.ext hk1))
  have hpow : ∀ {e : G}, orderOf e = 3 → ∀ x : ↥(Subgroup.zpowers e), x ^ 3 = 1 := by
    intro e he x
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 x.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      ← he, pow_orderOf_eq_one, one_zpow]
    rfl
  have hcard : Nat.card (↥(Subgroup.zpowers a) × (↥(Subgroup.zpowers b) ×
      ↥(Subgroup.zpowers w))) = 3 ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, Nat.card_zpowers, ha3,
      hb3, hw3]
    norm_num
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num)
    (fun p q => Prod.ext (mul_comm' p.1 q.1) (Prod.ext (mul_comm' p.2.1 q.2.1)
      (mul_comm' p.2.2 q.2.2)))
    (fun p => Prod.ext (hpow ha3 p.1) (Prod.ext (hpow hb3 p.2.1) (hpow hw3 p.2.2))) hcard f hf ?_
  rintro _ ⟨⟨⟨x, hx⟩, ⟨⟨y, hy⟩, ⟨z, hz⟩⟩⟩, rfl⟩
  rw [hfapp]
  exact X.mul_mem (Subgroup.zpowers_le.2 ha hx)
    (X.mul_mem (Subgroup.zpowers_le.2 hb hy) (Subgroup.zpowers_le.2 hw hz))

theorem false_of_two_blocks [Finite V] (hb : IsTransvectionBlocks J 𝓗)
    {X : Subgroup (MulAut V)} (hJX : J ≤ X) (h3 : CFSG.Open.pRank 3 X ≤ 2)
    {B₁ B₂ : Subgroup (MulAut V)} (h₁ : B₁ ∈ 𝓗) (h₂ : B₂ ∈ 𝓗) (hne : B₁ ≠ B₂)
    {w : MulAut V} (hwX : w ∈ X) (hw : orderOf w = 3)
    (hwc₁ : ∀ b ∈ B₁, w * b = b * w) (hwc₂ : ∀ b ∈ B₂, w * b = b * w)
    (hwf₁ : ∀ u ∈ commSub (⊤ : Subgroup V) B₁, w u = u)
    (hwf₂ : ∀ u ∈ commSub (⊤ : Subgroup V) B₂, w u = u) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨b₁, hb₁⟩, ho₁⟩ := exists_prime_orderOf_dvd_card' (G := ↥B₁) 3
    (by rw [hb.card_eq B₁ h₁]; norm_num)
  obtain ⟨⟨b₂, hb₂⟩, ho₂⟩ := exists_prime_orderOf_dvd_card' (G := ↥B₂) 3
    (by rw [hb.card_eq B₂ h₂]; norm_num)
  rw [Subgroup.orderOf_mk] at ho₁ ho₂
  have hle := three_le_pRank (X := X) (hJX (hb.le_J h₁ hb₁)) (hJX (hb.le_J h₂ hb₂)) hwX
    (hb.comm B₁ h₁ B₂ h₂ hne b₁ hb₁ b₂ hb₂) (hwc₁ b₁ hb₁).symm (hwc₂ b₂ hb₂).symm ho₁ ho₂ hw
    (fun i j k h => ?_)
  · omega
  have hfixk : ∀ u, w u = u → (w ^ k) u = u := fun u hu =>
    B1.zpowers_fix hu _ (Subgroup.zpow_mem_zpowers w k)
  constructor
  ·
    have hc : b₁ ^ i ∈ B₁ ⊓ centSub (commSub (⊤ : Subgroup V) B₁) := by
      refine ⟨B₁.zpow_mem hb₁ i, fun u hu => ?_⟩
      have h1 := congrArg (fun φ : MulAut V => φ u) h
      simp only [MulAut.mul_apply, MulAut.one_apply] at h1
      rwa [hfixk u (hwf₁ u hu),
        hb.triv B₂ h₂ B₁ h₁ hne.symm _ (B₂.zpow_mem hb₂ j) u hu] at h1
    rwa [hb.inf_centSub h₁, Subgroup.mem_bot] at hc
  ·
    have hc : b₂ ^ j ∈ B₂ ⊓ centSub (commSub (⊤ : Subgroup V) B₂) := by
      refine ⟨B₂.zpow_mem hb₂ j, fun u hu => ?_⟩
      have h1 := congrArg (fun φ : MulAut V => φ u) h
      simp only [MulAut.mul_apply, MulAut.one_apply] at h1
      have hbu : (b₂ ^ j) u ∈ commSub (⊤ : Subgroup V) B₂ :=
        hb.stab B₂ h₂ _ (B₂.zpow_mem hb₂ j) u hu
      rwa [hfixk u (hwf₂ u hu), hb.triv B₁ h₁ B₂ h₂ hne _ (B₁.zpow_mem hb₁ i) _ hbu] at h1
    rwa [hb.inf_centSub h₂, Subgroup.mem_bot] at hc

theorem card_blocks_le_two [Finite V] (hb : IsTransvectionBlocks J 𝓗) {X : Subgroup (MulAut V)}
    (hJX : J ≤ X) (h3 : CFSG.Open.pRank 3 X ≤ 2) : 𝓗.card ≤ 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨B₁, h₁, B₂, h₂, B₃, h₃, h12, h13, h23⟩ := Finset.two_lt_card.1 hcon
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨w, hw⟩, ho⟩ := exists_prime_orderOf_dvd_card' (G := ↥B₃) 3
    (by rw [hb.card_eq B₃ h₃]; norm_num)
  rw [Subgroup.orderOf_mk] at ho
  exact false_of_two_blocks hb hJX h3 h₁ h₂ h12 (hJX (hb.le_J h₃ hw)) ho
    (fun b hb' => hb.comm B₃ h₃ B₁ h₁ h13.symm w hw b hb')
    (fun b hb' => hb.comm B₃ h₃ B₂ h₂ h23.symm w hw b hb')
    (fun u hu => hb.triv B₃ h₃ B₁ h₁ h13.symm w hw u hu)
    (fun u hu => hb.triv B₃ h₃ B₂ h₂ h23.symm w hw u hu)

theorem exists_conj_mem_of_mul_self {G : Type*} [Group G] [Finite G] {X T₀ : Subgroup G}
    (hT₀ : IsSylowTwoOf T₀ X) {t : G} (htX : t ∈ X) (ht2 : t * t = 1) :
    ∃ x ∈ X, x * t * x⁻¹ ∈ T₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (Subgroup.zpowers t) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨1, Subtype.ext ?_⟩
    show (t ^ i) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, ht2,
      one_zpow]
  have hPX : Subgroup.zpowers t ≤ X := Subgroup.zpowers_le.2 htX
  have hP' : IsPGroup 2 ((Subgroup.zpowers t).subgroupOf X) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  have hS : IsSylowTwoOf ((Q : Subgroup X).map X.subtype) X := by
    refine ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map X.subtype, ?_⟩
    change ¬ 2 ∣ (Subgroup.comap X.subtype ((Q : Subgroup X).map X.subtype)).index
    rw [Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
    exact Sylow.not_dvd_index Q
  have htS : t ∈ (Q : Subgroup X).map X.subtype :=
    ⟨⟨t, htX⟩, hQ (show (⟨t, htX⟩ : X) ∈ (Subgroup.zpowers t).subgroupOf X from
      Subgroup.mem_zpowers t), rfl⟩
  obtain ⟨x, hxX, hTS⟩ := B1.sylowTwo_conj hS hT₀
  refine ⟨x, hxX, ?_⟩
  rw [hTS]
  exact ⟨t, htS, by simp [MulAut.conj_apply]⟩

theorem two_dvd_index_of_swap {X T₀ B₁ B₂ : Subgroup (MulAut V)} (hne : B₁ ≠ B₂)
    (hperm : ∀ x ∈ X, ∀ L, L = B₁ ∨ L = B₂ → B1.conjAut x L = B₁ ∨ B1.conjAut x L = B₂)
    {x₀ : MulAut V} (hx₀ : x₀ ∈ X) (hx₀B : B1.conjAut x₀ B₁ = B₂) (hT₀X : T₀ ≤ X)
    (hT₀ : ∀ s ∈ T₀, B1.conjAut s B₁ = B₁) : 2 ∣ (T₀.subgroupOf X).index := by
  have h₁ : B₁ = B₁ ∨ B₁ = B₂ := Or.inl rfl
  have h₂ : B₂ = B₁ ∨ B₂ = B₂ := Or.inr rfl
  set N : Subgroup (MulAut V) := X ⊓ Subgroup.normalizer (B₁ : Set (MulAut V)) with hN
  have hmemN : ∀ x ∈ X, x ∈ N ↔ B1.conjAut x B₁ = B₁ := fun x hx => by
    rw [hN, Subgroup.mem_inf, conjAut_eq_iff]
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  have hTN : T₀ ≤ N := fun s hs => (hmemN s (hT₀X hs)).2 (hT₀ s hs)
  have hNX : N ≤ X := inf_le_left
  have hidx : (N.subgroupOf X).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨x₀, hx₀⟩, fun b => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
      hmemN _ (X.mul_mem b.2 hx₀), hmemN _ b.2, conjAut_mul', hx₀B]
    rcases hperm b b.2 B₁ h₁ with hb1 | hb1 <;> rcases hperm b b.2 B₂ h₂ with hb2 | hb2
    · exact absurd (conjAut_inj (hb1.trans hb2.symm)) hne
    · exact Or.inr ⟨hb1, by rw [hb2]; exact hne.symm⟩
    · exact Or.inl ⟨hb2, by rw [hb1]; exact hne.symm⟩
    · exact absurd (conjAut_inj (hb1.trans hb2.symm)) hne
  have := Subgroup.relIndex_mul_relIndex T₀ N X hTN hNX
  refine ⟨T₀.relIndex N, ?_⟩
  rw [show (T₀.subgroupOf X).index = T₀.relIndex X from rfl, ← this,
    show N.relIndex X = (N.subgroupOf X).index from rfl, hidx, mul_comm]

theorem mem_sup_of_invariant {x : MulAut V} {A B : Subgroup V} (hA : ∀ a ∈ A, x a ∈ A)
    (hB : ∀ b ∈ B, x b ∈ B) {v : V} (hv : v ∈ A ⊔ B) : x v ∈ A ⊔ B := by
  have h : (A ⊔ B).map x.toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (Subgroup.map_le_iff_le_comap.2 fun a ha => hA a ha)
      (Subgroup.map_le_iff_le_comap.2 fun b hb => hB b hb)
  exact h (Subgroup.mem_map_of_mem _ hv)

theorem false_of_graph [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {B₁ B₂ : Subgroup (MulAut V)}
    (hb : IsTransvectionBlocks J 𝓗) (h₁ : B₁ ∈ 𝓗) (h₂ : B₂ ∈ 𝓗) (hne : B₁ ≠ B₂)
    (hCP : fixV J ⊔ (commSub (⊤ : Subgroup V) B₁ ⊔ commSub (⊤ : Subgroup V) B₂) = ⊤)
    {W : Subgroup V} (hW : Nat.card W = 4)
    (hWP : W ≤ commSub (⊤ : Subgroup V) B₁ ⊔ commSub (⊤ : Subgroup V) B₂)
    (hW1 : W ⊓ commSub (⊤ : Subgroup V) B₁ = ⊥) (hW2 : W ⊓ commSub (⊤ : Subgroup V) B₂ = ⊥)
    {t₁ : MulAut V} (ht₁ : t₁ ∈ B₁) (ht₁1 : t₁ ≠ 1) (ht₁W : ∀ w ∈ W, t₁ w ∈ W) : False := by
  have hfixW : ∀ w ∈ W, t₁ w = w := by
    intro w hw
    have h1 : t₁ w * w⁻¹ ∈ W ⊓ commSub (⊤ : Subgroup V) B₁ :=
      ⟨W.mul_mem (ht₁W w hw) (W.inv_mem hw),
        Subgroup.subset_closure ⟨t₁, ht₁, w, Subgroup.mem_top w, rfl⟩⟩
    rw [hW1, Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1
  have hU12 : commSub (⊤ : Subgroup V) B₁ ⊓ commSub (⊤ : Subgroup V) B₂ = ⊥ := by
    rw [eq_bot_iff, ← hb.fixV_inf_commSub hV h₂]
    exact inf_le_inf_right _ fun u hu => mem_fixV.2 fun a ha =>
      hb.triv B₂ h₂ B₁ h₁ hne.symm a ha u hu
  have hc1 := card_sup_mul_card_inf (commSub (⊤ : Subgroup V) B₁) (commSub (⊤ : Subgroup V) B₂)
  have hc2 := card_sup_mul_card_inf W (commSub (⊤ : Subgroup V) B₂)
  rw [hU12, Subgroup.card_bot, mul_one, hb.card_comm B₁ h₁, hb.card_comm B₂ h₂] at hc1
  rw [hW2, Subgroup.card_bot, mul_one, hW, hb.card_comm B₂ h₂] at hc2
  have hWU : W ⊔ commSub (⊤ : Subgroup V) B₂ =
      commSub (⊤ : Subgroup V) B₁ ⊔ commSub (⊤ : Subgroup V) B₂ :=
    Subgroup.eq_of_le_of_card_ge (sup_le hWP le_sup_right) (by rw [hc1, hc2])
  apply ht₁1
  have hle : (W ⊔ commSub (⊤ : Subgroup V) B₂) ⊔ fixV J ≤ fixV (Subgroup.zpowers t₁) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact fun w hw => mem_fixV.2 fun y hy => B1.zpowers_fix (hfixW w hw) y hy
    · exact fun u hu => mem_fixV.2 fun y hy =>
        B1.zpowers_fix (hb.triv B₁ h₁ B₂ h₂ hne t₁ ht₁ u hu) y hy
    · exact fun v hv => mem_fixV.2 fun y hy => B1.zpowers_fix (hv t₁ (hb.le_J h₁ ht₁)) y hy
  rw [hWU, sup_comm, hCP] at hle
  exact MulEquiv.ext fun v => hle (Subgroup.mem_top v) t₁ (Subgroup.mem_zpowers t₁)

theorem eq_top_of_le_commSub [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X T₀ B₁ B₂ : Subgroup (MulAut V)}
    {𝓗 : Finset (Subgroup (MulAut V))}
    (hb : IsTransvectionBlocks (Subgroup.closure (transvectionsIn X)) 𝓗) (h₁ : B₁ ∈ 𝓗)
    (h₂ : B₂ ∈ 𝓗) (hne : B₁ ≠ B₂) (h𝓗 : ∀ L ∈ 𝓗, L = B₁ ∨ L = B₂)
    (hT₀ : IsSylowTwoOf T₀ X) {W : Subgroup V} (hW : Nat.card W = 4)
    (hTW : ∀ s ∈ T₀, ∀ w ∈ W, s w ∈ W)
    (hgen : (⨆ m ∈ X, W.map (m : MulAut V).toMonoidHom) = ⊤)
    (hW1 : W ≤ commSub (⊤ : Subgroup V) B₁) : W = ⊤ := by
  have hWeq : W = commSub (⊤ : Subgroup V) B₁ :=
    Subgroup.eq_of_le_of_card_ge hW1 (by rw [hb.card_comm B₁ h₁, hW])
  have hperm : ∀ x ∈ X, ∀ L, L = B₁ ∨ L = B₂ → B1.conjAut x L = B₁ ∨ B1.conjAut x L = B₂ := by
    intro x hx L hL
    have hL' : L ∈ 𝓗 := by rcases hL with rfl | rfl <;> assumption
    obtain ⟨L', hL'', hLeq⟩ := hb.exists_conjAut_eq hV hL' hx
    rw [hLeq]
    exact h𝓗 L' hL''
  have hT1 : ∀ s ∈ T₀, B1.conjAut s B₁ = B₁ := by
    intro s hs
    rcases hperm s (hT₀.1 hs) B₁ (Or.inl rfl) with h | h
    · exact h
    · exfalso
      have hle : commSub (⊤ : Subgroup V) B₂ ≤ fixV B₁ ⊓ commSub (⊤ : Subgroup V) B₁ := by
        intro u hu
        refine ⟨mem_fixV.2 fun a ha => hb.triv B₁ h₁ B₂ h₂ hne a ha u hu, ?_⟩
        rw [← h, ← IsTransvectionBlocks.map_commSub_conjAut] at hu
        obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
        rw [← hWeq] at hu' ⊢
        exact hTW s hs u' hu'
      rw [hb.fixV_inf_commSub hV h₁, le_bot_iff] at hle
      have := hb.card_comm B₂ h₂
      rw [hle, Subgroup.card_bot] at this
      omega
  by_cases hall : ∀ x ∈ X, B1.conjAut x B₁ = B₁
  · refine eq_top_of_invariant hgen le_rfl fun x hx w hw => ?_
    rw [hWeq] at hw ⊢
    exact mem_commSub_of_conjAut (hall x hx) hw
  · exfalso
    push Not at hall
    obtain ⟨x₀, hx₀, hx₀B⟩ := hall
    have hx₀B' : B1.conjAut x₀ B₁ = B₂ := (hperm x₀ hx₀ B₁ (Or.inl rfl)).resolve_left hx₀B
    exact hT₀.2.2 (two_dvd_index_of_swap hne hperm hx₀ hx₀B' hT₀.1 hT1)

theorem eq_top_of_transvection [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X T₀ : Subgroup (MulAut V)} (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    (h3 : CFSG.Open.pRank 3 X ≤ 2) (hT₀ : IsSylowTwoOf T₀ X) {t : MulAut V} (htX : t ∈ X)
    (ht : IsTransvection t) {W : Subgroup V} (hW : Nat.card W = 4) {c : MulAut V} (hcX : c ∈ X)
    {n : ℕ} (hcn : c ^ 3 ^ n = 1) (hcW : ∀ w ∈ W, c w ∈ W) (hfix : ∀ w ∈ W, c w = w → w = 1)
    (hTW : ∀ s ∈ T₀, ∀ w ∈ W, s w ∈ W)
    (hgen : (⨆ m ∈ X, W.map (m : MulAut V).toMonoidHom) = ⊤) : W = ⊤ := by
  classical
  set J := Subgroup.closure (transvectionsIn X) with hJdef
  have hJX : J ≤ X := B1.closure_transvectionsIn_le X
  have hJn : ∀ x ∈ X, ∀ j ∈ J, x * j * x⁻¹ ∈ J :=
    fun x hx j hj => B1.closure_transvectionsIn_normal x hx j hj
  have hsolvJ : Group.IsSolvable ↥J := B1.solvable_of_le hJX hsolv
  have hOJ := B1.normal_two_subgroups_trivial_of_normal hJX hJn hO2
  have hcl : Subgroup.closure (transvectionsIn J) = J := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 fun t ht => ht.1
    · exact Subgroup.closure_mono fun t ht => ⟨Subgroup.subset_closure ht, ht.2⟩
  obtain ⟨𝓗, hb⟩ := transvection_structure hV hsolvJ hOJ hcl
  have htJ : t ∈ J := Subgroup.subset_closure ⟨htX, ht⟩
  obtain ⟨hCP, hCP'⟩ : fixV J ⊔ (⨆ L ∈ 𝓗, commSub (⊤ : Subgroup V) L) = ⊤ ∧
      fixV J ⊓ (⨆ L ∈ 𝓗, commSub (⊤ : Subgroup V) L) = ⊥ := by
    have := hb.decomp hV 𝓗 subset_rfl
    rwa [hb.iSup_eq] at this
  have hcardV : Nat.card (fixV J) * Nat.card ↥(⨆ L ∈ 𝓗, commSub (⊤ : Subgroup V) L) =
      Nat.card V := by
    have := card_sup_mul_card_inf (fixV J) (⨆ L ∈ 𝓗, commSub (⊤ : Subgroup V) L)
    rw [hCP, hCP', Subgroup.card_bot, Subgroup.card_top, mul_one] at this
    exact this.symm
  have hCX : ∀ x ∈ X, ∀ v ∈ fixV J, x v ∈ fixV J := by
    intro x hx v hv
    refine mem_fixV.2 fun j hj => ?_
    have h1 : x⁻¹ * j * x ∈ J := by simpa using hJn x⁻¹ (X.inv_mem hx) j hj
    have h2 := hv _ h1
    calc j (x v) = x (x⁻¹ (j (x v))) := (MulAut.apply_inv_self V x _).symm
      _ = x ((x⁻¹ * j * x) v) := rfl
      _ = x v := by rw [h2]
  have hWC : W ⊓ fixV J = ⊥ := by
    rcases inf_eq_bot_or_le hW hcW hfix (hCX c hcX) with h | h
    · exact h
    · exfalso
      have hCt := eq_top_of_invariant hgen h hCX
      apply ht.1
      refine MulEquiv.ext fun v => ?_
      have : v ∈ fixV J := hCt ▸ Subgroup.mem_top v
      exact this t htJ
  have ht2 : t * t = 1 := by
    obtain ⟨ht1, w, htw⟩ := ht
    exact B1.tv_sq hV htw ht1
  obtain ⟨x, hxX, ht₁T⟩ := exists_conj_mem_of_mul_self hT₀ htX ht2
  have ht₁ : IsTransvection (x * t * x⁻¹) := B1.isTransvection_conj ht x
  have ht₁J : x * t * x⁻¹ ∈ J := hJn x hxX t htJ
  have hne : 𝓗.Nonempty := by
    obtain ⟨B, hB, -⟩ := hb.cover t ⟨htJ, ht⟩
    exact ⟨B, hB⟩
  have hcases : 𝓗.card = 1 ∨ 𝓗.card = 2 := by
    have h1 := hne.card_pos
    have h2 := card_blocks_le_two hb hJX h3
    omega
  rcases hcases with h1 | h2
  ·
    obtain ⟨B, rfl⟩ := Finset.card_eq_one.1 h1
    have hBmem : B ∈ ({B} : Finset (Subgroup (MulAut V))) := Finset.mem_singleton_self B
    have hPB : (⨆ L ∈ ({B} : Finset (Subgroup (MulAut V))), commSub (⊤ : Subgroup V) L) =
        commSub (⊤ : Subgroup V) B := Finset.iSup_singleton _ _
    have hJB : J = B := by
      have := hb.iSup_eq
      rw [Finset.iSup_singleton] at this
      exact this.symm
    rw [hPB] at hcardV
    have hPX : ∀ x ∈ X, ∀ v ∈ commSub (⊤ : Subgroup V) B, x v ∈ commSub (⊤ : Subgroup V) B := by
      intro x hx v hv
      obtain ⟨L, hL, hLeq⟩ := hb.exists_conjAut_eq hV hBmem hx
      rw [Finset.mem_singleton] at hL
      rw [hL] at hLeq
      exact mem_commSub_of_conjAut hLeq hv
    rcases inf_eq_bot_or_le hW hcW hfix (hPX c hcX) with hWP | hWP
    ·
      exfalso
      have hfixW : ∀ w ∈ W, (x * t * x⁻¹) w = w := by
        intro w hw
        have h1 : (x * t * x⁻¹) w * w⁻¹ ∈ W ⊓ commSub (⊤ : Subgroup V) B :=
          ⟨W.mul_mem (hTW _ ht₁T w hw) (W.inv_mem hw),
            Subgroup.subset_closure ⟨_, hJB ▸ ht₁J, w, Subgroup.mem_top w, rfl⟩⟩
        rw [hWP, Subgroup.mem_bot, mul_inv_eq_one] at h1
        exact h1
      have hWCtop : W ⊔ fixV J = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        have := card_sup_mul_card_inf W (fixV J)
        rw [hWC, Subgroup.card_bot, mul_one, hW] at this
        rw [this, ← hcardV, hb.card_comm B hBmem, mul_comm]
      apply ht₁.1
      have hle : W ⊔ fixV J ≤ fixV (Subgroup.zpowers (x * t * x⁻¹)) := by
        refine sup_le ?_ ?_
        · exact fun w hw => mem_fixV.2 fun y hy => B1.zpowers_fix (hfixW w hw) y hy
        · exact fun v hv => mem_fixV.2 fun y hy => B1.zpowers_fix (hv _ ht₁J) y hy
      rw [hWCtop] at hle
      exact MulEquiv.ext fun v => hle (Subgroup.mem_top v) _ (Subgroup.mem_zpowers _)
    ·
      have hWeq : W = commSub (⊤ : Subgroup V) B :=
        Subgroup.eq_of_le_of_card_ge hWP (by rw [hb.card_comm B hBmem, hW])
      exact eq_top_of_invariant hgen le_rfl (hWeq ▸ hPX)
  ·
    obtain ⟨B₁, B₂, hne12, rfl⟩ := Finset.card_eq_two.1 h2
    have h₁ : B₁ ∈ ({B₁, B₂} : Finset (Subgroup (MulAut V))) := Finset.mem_insert_self _ _
    have h₂ : B₂ ∈ ({B₁, B₂} : Finset (Subgroup (MulAut V))) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have h𝓗 : ∀ L ∈ ({B₁, B₂} : Finset (Subgroup (MulAut V))), L = B₁ ∨ L = B₂ := by
      intro L hL
      simpa using hL
    have h𝓗' : ∀ L ∈ ({B₁, B₂} : Finset (Subgroup (MulAut V))), L = B₂ ∨ L = B₁ :=
      fun L hL => (h𝓗 L hL).symm
    have hPB : (⨆ L ∈ ({B₁, B₂} : Finset (Subgroup (MulAut V))), commSub (⊤ : Subgroup V) L) =
        commSub (⊤ : Subgroup V) B₁ ⊔ commSub (⊤ : Subgroup V) B₂ := by
      rw [Finset.iSup_insert, Finset.iSup_singleton]
    rw [hPB] at hCP
    have hperm : ∀ y ∈ X, ∀ L ∈ ({B₁, B₂} : Finset (Subgroup (MulAut V))),
        B1.conjAut y L = B₁ ∨ B1.conjAut y L = B₂ := by
      intro y hy L hL
      obtain ⟨L', hL', hLeq⟩ := hb.exists_conjAut_eq hV hL hy
      rw [hLeq]
      exact h𝓗 L' hL'
    have hc2 : ∀ L ∈ ({B₁, B₂} : Finset (Subgroup (MulAut V))), B1.conjAut (c * c) L = L := by
      intro L hL
      rw [conjAut_mul']
      rcases h𝓗 L hL with rfl | rfl
      · rcases hperm c hcX L h₁ with h | h
        · rw [h, h]
        · rcases hperm c hcX B₂ h₂ with h' | h'
          · rw [h, h']
          · exact absurd (conjAut_inj (h.trans h'.symm)) hne12
      · rcases hperm c hcX L h₂ with h | h
        · rcases hperm c hcX B₁ h₁ with h' | h'
          · exact absurd (conjAut_inj (h'.trans h.symm)) hne12
          · rw [h, h']
        · rw [h, h]
    have hcB : ∀ L ∈ ({B₁, B₂} : Finset (Subgroup (MulAut V))), B1.conjAut c L = L := by
      intro L hL
      have hpow : ∀ m : ℕ, B1.conjAut ((c * c) ^ m) L = L := by
        intro m
        induction m with
        | zero =>
          ext y
          simp [B1.mem_conjAut]
        | succ m ih => rw [pow_succ, conjAut_mul', hc2 L hL, ih]
      obtain ⟨m, hm⟩ : Odd (3 ^ n) := Odd.pow (by decide)
      have hcc : (c * c) ^ (m + 1) = c := by
        rw [← sq, ← pow_mul, show 2 * (m + 1) = 3 ^ n + 1 by omega, pow_succ, hcn, one_mul]
      rw [← hcc]
      exact hpow (m + 1)
    obtain ⟨k₁, hk₁, hk₁3, hck₁⟩ := exists_inner hb h₁ (hcB B₁ h₁) hcn
    obtain ⟨k₂, hk₂, hk₂3, hck₂⟩ := exists_inner hb h₂ (hcB B₂ h₂) hcn
    have hk₂b₁ : ∀ b ∈ B₁, k₂ * b = b * k₂ :=
      fun b hb' => hb.comm B₂ h₂ B₁ h₁ hne12.symm k₂ hk₂ b hb'
    have hk₂u₁ : ∀ u ∈ commSub (⊤ : Subgroup V) B₁, k₂ u = u :=
      fun u hu => hb.triv B₂ h₂ B₁ h₁ hne12.symm k₂ hk₂ u hu
    have hk₁b₂ : ∀ b ∈ B₂, k₁ * b = b * k₁ := fun b hb' => hb.comm B₁ h₁ B₂ h₂ hne12 k₁ hk₁ b hb'
    have hk₁u₂ : ∀ u ∈ commSub (⊤ : Subgroup V) B₂, k₁ u = u :=
      fun u hu => hb.triv B₁ h₁ B₂ h₂ hne12 k₁ hk₁ u hu
    obtain ⟨hzb₁, hzu₁⟩ := absorb hb h₁ (hcB B₁ h₁) hk₁ hck₁ hk₂b₁ hk₂u₁
    obtain ⟨hzb₂, hzu₂⟩ := absorb hb h₂ (hcB B₂ h₂) hk₂ hck₂ hk₁b₂ hk₁u₂
    have hk12 : k₂ * k₁ = k₁ * k₂ := (hk₁b₂ k₂ hk₂).symm
    rw [hk12] at hzb₂ hzu₂
    have hcom : ∀ {k : MulAut V} {L : Subgroup (MulAut V)}, L ∈ ({B₁, B₂} : Finset _) →
        k ∈ L → (∀ v ∈ commSub (⊤ : Subgroup V) L, c v = k v) → Commute c k := by
      intro k L hL hkL hck
      have := conj_eq_of_inner hb hL (hcB L hL) hkL hck hkL
      calc c * k = (c * k * c⁻¹) * c := by group
        _ = (k * k * k⁻¹) * c := by rw [this]
        _ = k * c := by group
    have hc12 : Commute c (k₁ * k₂) := (hcom h₁ hk₁ hck₁).mul_right (hcom h₂ hk₂ hck₂)
    have hk12pow : (k₁ * k₂) ^ 3 ^ (n + 1) = 1 := by
      rw [pow_succ', pow_mul, (show Commute k₁ k₂ from hk₁b₂ k₂ hk₂).mul_pow, hk₁3, hk₂3,
        mul_one, one_pow]
    have hcpow : c ^ 3 ^ (n + 1) = 1 := by rw [pow_succ, pow_mul, hcn, one_pow]
    have hzpow : ((k₁ * k₂)⁻¹ * c) ^ 3 ^ (n + 1) = 1 := by
      rw [(hc12.symm.inv_left).mul_pow, inv_pow, hk12pow, hcpow, inv_one, one_mul]
    have hzX : (k₁ * k₂)⁻¹ * c ∈ X := X.mul_mem (X.inv_mem (X.mul_mem
      (hJX (hb.le_J h₁ hk₁)) (hJX (hb.le_J h₂ hk₂)))) hcX
    have hz1 : (k₁ * k₂)⁻¹ * c = 1 := by
      by_contra hz1
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hdvd : 3 ∣ Nat.card (Subgroup.zpowers ((k₁ * k₂)⁻¹ * c)) := by
        rw [Nat.card_zpowers]
        obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
          (orderOf_dvd_of_pow_eq_one hzpow)
        rw [hj']
        rcases j with _ | j
        · exact absurd (orderOf_eq_one_iff.1 (by rw [hj', pow_zero])) hz1
        · exact dvd_pow_self 3 (Nat.succ_ne_zero j)
      obtain ⟨⟨w, hw⟩, hwo⟩ := exists_prime_orderOf_dvd_card'
        (G := ↥(Subgroup.zpowers ((k₁ * k₂)⁻¹ * c))) 3 hdvd
      rw [Subgroup.orderOf_mk] at hwo
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      exact false_of_two_blocks hb hJX h3 h₁ h₂ hne12 (X.zpow_mem hzX i) hwo
        (fun b hb' => (show Commute ((k₁ * k₂)⁻¹ * c) b from hzb₁ b hb').zpow_left i)
        (fun b hb' => (show Commute ((k₁ * k₂)⁻¹ * c) b from hzb₂ b hb').zpow_left i)
        (fun u hu => B1.zpowers_fix (hzu₁ u hu) _ (Subgroup.zpow_mem_zpowers _ i))
        (fun u hu => B1.zpowers_fix (hzu₂ u hu) _ (Subgroup.zpow_mem_zpowers _ i))
    have hcJ : c = k₁ * k₂ := (inv_mul_eq_one.1 hz1).symm
    have hPc : ∀ v ∈ commSub (⊤ : Subgroup V) B₁ ⊔ commSub (⊤ : Subgroup V) B₂,
        c v ∈ commSub (⊤ : Subgroup V) B₁ ⊔ commSub (⊤ : Subgroup V) B₂ :=
      fun v hv => mem_sup_of_invariant (fun u hu => mem_commSub_of_conjAut (hcB B₁ h₁) hu)
        (fun u hu => mem_commSub_of_conjAut (hcB B₂ h₂) hu) hv
    have hWP : W ≤ commSub (⊤ : Subgroup V) B₁ ⊔ commSub (⊤ : Subgroup V) B₂ := by
      rcases inf_eq_bot_or_le hW hcW hfix hPc with h | h
      · exfalso
        have hW1 : W = ⊥ := by
          rw [eq_bot_iff]
          intro w hw
          have h1 : c w * w⁻¹ ∈ W ⊓ (commSub (⊤ : Subgroup V) B₁ ⊔
              commSub (⊤ : Subgroup V) B₂) := by
            refine ⟨W.mul_mem (hcW w hw) (W.inv_mem hw), ?_⟩
            have e : c w * w⁻¹ = (k₁ (k₂ w) * (k₂ w)⁻¹) * (k₂ w * w⁻¹) := by
              rw [hcJ, MulAut.mul_apply]
              group
            rw [e]
            exact Subgroup.mul_mem _
              (Subgroup.mem_sup_left (Subgroup.subset_closure
                ⟨k₁, hk₁, k₂ w, Subgroup.mem_top _, rfl⟩))
              (Subgroup.mem_sup_right (Subgroup.subset_closure
                ⟨k₂, hk₂, w, Subgroup.mem_top _, rfl⟩))
          rw [h, Subgroup.mem_bot, mul_inv_eq_one] at h1
          exact hfix w hw h1
        rw [hW1, Subgroup.card_bot] at hW
        omega
      · exact h
    rcases inf_eq_bot_or_le hW hcW hfix
        (fun u hu => mem_commSub_of_conjAut (hcB B₁ h₁) hu) with hW1 | hW1
    · rcases inf_eq_bot_or_le hW hcW hfix
          (fun u hu => mem_commSub_of_conjAut (hcB B₂ h₂) hu) with hW2 | hW2
      · exfalso
        obtain ⟨L, hL, ht₁L⟩ := hb.cover _ ⟨ht₁J, ht₁⟩
        rcases h𝓗 L hL with rfl | rfl
        · exact false_of_graph hV hb h₁ h₂ hne12 hCP hW hWP hW1 hW2 ht₁L ht₁.1
            (hTW _ ht₁T)
        · exact false_of_graph hV hb h₂ h₁ hne12.symm (by rwa [sup_comm (commSub ⊤ L)])
            hW (by rwa [sup_comm]) hW2 hW1 ht₁L ht₁.1 (hTW _ ht₁T)
      · exact eq_top_of_le_commSub hV hb h₂ h₁ hne12.symm h𝓗' hT₀ hW hTW hgen hW2
    · exact eq_top_of_le_commSub hV hb h₁ h₂ hne12 h𝓗 hT₀ hW hTW hgen hW1

end A6Tv

end CFSG.Quasithin.H13.A6

