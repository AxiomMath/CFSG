module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1LnB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardASet
public import CFSG.LargeExtraspecial.S12InspFamSmall

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

private theorem s1611e3_isElemAbelian_open_of_isElemAbelian2 {V : Type} [CommGroup V]
    {A : Subgroup (MulAut V)} (h : IsElemAbelian2 A) : CFSG.Open.IsElemAbelian 2 A :=
  ⟨⟨⟨fun a b => Subtype.ext (h.1 a.1 a.2 b.1 b.2)⟩⟩, fun x hx => h.2 x hx⟩

private theorem s1611e3_zpowers_subgroupOf {A : Type*} [Group A] {L : Subgroup A} (x : A)
    (hx : x ∈ L) : (Subgroup.zpowers x).subgroupOf L = Subgroup.zpowers ⟨x, hx⟩ := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩

private theorem s1611e3_map_zpowers_subgroupOf {A B : Type*} [Group A] [Group B]
    {L : Subgroup A} (f : ↥L →* B) (x : A) (hx : x ∈ L) :
    ((Subgroup.zpowers x).subgroupOf L).map f = Subgroup.zpowers (f ⟨x, hx⟩) := by
  rw [s1611e3_zpowers_subgroupOf x hx, MonoidHom.map_zpowers]

private theorem s1611e3_fixV_prod_map {W : Type} [CommGroup W] {J₀ : Subgroup W}
    {L : Subgroup (MulAut W)} (φ : ↥L →* MulAut ↥J₀) (Θ : ↥J₀ × ↥J₀ ≃* W)
    (hΘ : ∀ (l : ↥L) (p : ↥J₀ × ↥J₀), (l : MulAut W) (Θ p) = Θ (φ l p.1, φ l p.2))
    (B : Subgroup (MulAut W)) (hB : B ≤ L) :
    fixV B = ((fixV ((B.subgroupOf L).map φ)).prod
      (fixV ((B.subgroupOf L).map φ))).map (Θ : ↥J₀ × ↥J₀ →* W) := by
  ext w
  constructor
  · intro hw
    have hcoord : ∀ b : MulAut ↥J₀, b ∈ (B.subgroupOf L).map φ →
        b (Θ.symm w).1 = (Θ.symm w).1 ∧ b (Θ.symm w).2 = (Θ.symm w).2 := by
      intro b hb
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hb
      have hfix := mem_fixV.mp hw (l : MulAut W) (Subgroup.mem_subgroupOf.mp hl)
      have hp : Θ.symm w = (φ l (Θ.symm w).1, φ l (Θ.symm w).2) := by
        apply Θ.injective
        rw [MulEquiv.apply_symm_apply, ← hΘ l (Θ.symm w), MulEquiv.apply_symm_apply, hfix]
      exact ⟨(congrArg Prod.fst hp).symm, (congrArg Prod.snd hp).symm⟩
    refine Subgroup.mem_map.mpr ⟨Θ.symm w, Subgroup.mem_prod.mpr ⟨?_, ?_⟩,
      Θ.apply_symm_apply w⟩
    · exact mem_fixV.mpr fun b hb => (hcoord b hb).1
    · exact mem_fixV.mpr fun b hb => (hcoord b hb).2
  · intro hw
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hw
    refine mem_fixV.mpr ?_
    intro b hb
    have hp1 : p.1 ∈ fixV ((B.subgroupOf L).map φ) := (Subgroup.mem_prod.mp hp).1
    have hp2 : p.2 ∈ fixV ((B.subgroupOf L).map φ) := (Subgroup.mem_prod.mp hp).2
    have hmem : φ ⟨b, hB hb⟩ ∈ (B.subgroupOf L).map φ :=
      Subgroup.mem_map.mpr ⟨⟨b, hB hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    have h1 : φ ⟨b, hB hb⟩ p.1 = p.1 := mem_fixV.mp hp1 _ hmem
    have h2 : φ ⟨b, hB hb⟩ p.2 = p.2 := mem_fixV.mp hp2 _ hmem
    change ((⟨b, hB hb⟩ : ↥L) : MulAut W) (Θ p) = Θ p
    rw [hΘ ⟨b, hB hb⟩ p, h1, h2]

private theorem s1611e3_perm3_involution :
    ∀ σ : Equiv.Perm (Fin 3), σ * σ = 1 → σ ≠ 1 →
      σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 0 2 ∨ σ = Equiv.swap 1 2 := by
  decide +kernel

private theorem s1611e3_rk_le_two_of_aSet_two {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {X K L₀ : Subgroup (MulAut W)} (hK : IsSym ↥K 3)
    (hdir : IsInternalDirect K L₀ X) (hL₀ : IsLn ↥L₀ 3 1)
    {E : Subgroup (MulAut W)} (hE : E ∈ E3.aSet 2 X) : rk ↥E ≤ 2 := by
  have hEL : E ≤ L₀ := s16c11_v1_aSet_le_right hW hK hdir hE
  have hEab0 : CFSG.Open.IsElemAbelian 2 E :=
    s1611e3_isElemAbelian_open_of_isElemAbelian2 hE.2.2.1
  have hEab : CFSG.Open.IsElemAbelian 2 (E.subgroupOf L₀) :=
    CFSG.Open.IsElemAbelian.subgroupOf hEab0 L₀
  have h4 := CFSG.LargeExtraspecial.S12Insp5.card_le_four_of_lieModel_PSL32 hL₀
    (E.subgroupOf L₀) hEab
  have hcard : Nat.card ↥E ≤ 4 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv]
    exact h4
  have hE2 : ∀ v : ↥E, v ^ 2 = 1 := fun v => Subtype.ext (hE.2.2.1.2 (v : MulAut W) v.2)
  have hcardE : Nat.card ↥E = 2 ^ rk ↥E :=
    CFSG.Quasithin.card_eq_two_pow_of_isPGroup
      (CFSG.Quasithin.isPGroup_two_of_sq_eq_one hE2)
  have h2 : 2 ^ rk ↥E ≤ 2 ^ 2 := by
    rw [← hcardE]
    simpa using hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2

private theorem s1611e3_coord_action {W : Type} [CommGroup W]
    {K L₀ : Subgroup (MulAut W)} {J₀ : Subgroup W}
    (s : ↥K ≃* Equiv.Perm (Fin 3)) (ψ : W ≃* ↥(s16c2m_Triples ↥J₀))
    (hs : ∀ (κ : ↥K) (w : W) (i : Fin 3),
      (ψ ((κ : MulAut W) w)).1 i = (ψ w).1 ((s κ)⁻¹ i))
    (hg : ∀ g ∈ L₀, ∀ (w : W) (i : Fin 3),
      (((ψ (g w)).1 i : ↥J₀) : W) = g (((ψ w).1 i : ↥J₀) : W))
    {κ ℓ : MulAut W} (hκ : κ ∈ K) (hℓ : ℓ ∈ L₀) (w : W) (m : Fin 3) :
    (((ψ ((κ * ℓ) w)).1 m : ↥J₀) : W) = ℓ (((ψ w).1 ((s ⟨κ, hκ⟩)⁻¹ m) : ↥J₀) : W) := by
  rw [MulAut.mul_apply, hs ⟨κ, hκ⟩ (ℓ w) m]
  exact hg ℓ hℓ w ((s ⟨κ, hκ⟩)⁻¹ m)

private theorem s1611e3_coords {W : Type} [CommGroup W] {J₀ : Subgroup W}
    (hW : ∀ w : W, w ^ 2 = 1) (u : ↥(s16c2m_Triples ↥J₀)) :
    u.1 0 = u.1 1 * u.1 2 ∧ u.1 1 = u.1 0 * u.1 2 ∧ u.1 2 = u.1 0 * u.1 1 := by
  have h := (s16c2m_mem_Triples_iff u.1).1 u.2
  have hsq : ∀ x : ↥J₀, x * x = 1 := fun x => Subtype.ext (by simpa [pow_two] using hW (x : W))
  have hinv : ∀ x : ↥J₀, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  have key : ∀ a b c : ↥J₀, a * b * c = 1 → (a = b * c ∧ b = a * c ∧ c = a * b) := by
    intro a b c h
    have hc : c = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right h
    have hb : b = (a * c)⁻¹ := by
      have h1 : a * c * b = 1 := by rw [← h]; ac_rfl
      exact eq_inv_of_mul_eq_one_right h1
    have ha : a = (b * c)⁻¹ := by
      have h1 : b * c * a = 1 := by rw [← h]; ac_rfl
      exact eq_inv_of_mul_eq_one_right h1
    refine ⟨?_, ?_, ?_⟩
    · rw [ha, mul_inv_rev, hinv b, hinv c, mul_comm]
    · rw [hb, mul_inv_rev, hinv a, hinv c, mul_comm]
    · rw [hc, mul_inv_rev, hinv a, hinv b, mul_comm]
  exact key (u.1 0) (u.1 1) (u.1 2) h

private theorem s1611e3_coordsW {W : Type} [CommGroup W] {J₀ : Subgroup W}
    (hW : ∀ w : W, w ^ 2 = 1) (u : ↥(s16c2m_Triples ↥J₀)) :
    ((u.1 0 : W) = (u.1 1 : W) * (u.1 2 : W)) ∧
      ((u.1 1 : W) = (u.1 0 : W) * (u.1 2 : W)) ∧
      ((u.1 2 : W) = (u.1 0 : W) * (u.1 1 : W)) := by
  obtain ⟨h0, h1, h2⟩ := s1611e3_coords hW u
  exact ⟨by simpa using congrArg (fun x : ↥J₀ => (x : W)) h0,
    by simpa using congrArg (fun x : ↥J₀ => (x : W)) h1,
    by simpa using congrArg (fun x : ↥J₀ => (x : W)) h2⟩

private theorem s1611e3_coord_swap01 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {K L₀ : Subgroup (MulAut W)} {J₀ : Subgroup W}
    (s : ↥K ≃* Equiv.Perm (Fin 3)) (ψ : W ≃* ↥(s16c2m_Triples ↥J₀))
    (hs : ∀ (κ : ↥K) (w : W) (i : Fin 3),
      (ψ ((κ : MulAut W) w)).1 i = (ψ w).1 ((s κ)⁻¹ i))
    (hg : ∀ g ∈ L₀, ∀ (w : W) (i : Fin 3),
      (((ψ (g w)).1 i : ↥J₀) : W) = g (((ψ w).1 i : ↥J₀) : W))
    {κ ℓ : MulAut W} (hκ : κ ∈ K) (hσ : s ⟨κ, hκ⟩ = Equiv.swap 0 1) (hℓ : ℓ ∈ L₀) :
    Nat.card ↥(fixV (Subgroup.zpowers (κ * ℓ))) ≤ Nat.card ↥J₀ := by
  have hσinv : (s ⟨κ, hκ⟩)⁻¹ = Equiv.swap 0 1 := by rw [hσ]; decide
  have hfixcoord : ∀ w ∈ fixV (Subgroup.zpowers (κ * ℓ)), ∀ m : Fin 3,
      (((ψ w).1 m : ↥J₀) : W) = ℓ (((ψ w).1 (Equiv.swap 0 1 m) : ↥J₀) : W) := by
    intro w hw m
    have h1 := s1611e3_coord_action s ψ hs hg hκ hℓ w m
    rw [hσinv] at h1
    have h2 : (κ * ℓ) w = w := (mem_fixV.mp hw) (κ * ℓ) (Subgroup.mem_zpowers _)
    rwa [h2] at h1
  refine Nat.card_le_card_of_injective
    (fun w : ↥(fixV (Subgroup.zpowers (κ * ℓ))) => (ψ (w : W)).1 0) ?_
  intro w w' h
  beta_reduce at h
  apply Subtype.ext
  apply ψ.injective
  apply Subtype.ext
  funext m
  fin_cases m
  · apply Subtype.ext
    exact congrArg (fun x : ↥J₀ => (x : W)) h
  · apply Subtype.ext
    show ((ψ (w : W)).1 1 : W) = ((ψ (w' : W)).1 1 : W)
    have h1 : ((ψ (w : W)).1 1 : W) = ℓ (((ψ (w : W)).1 0 : ↥J₀) : W) := by
      simpa using hfixcoord (w : W) w.2 1
    have h1' : ((ψ (w' : W)).1 1 : W) = ℓ (((ψ (w' : W)).1 0 : ↥J₀) : W) := by
      simpa using hfixcoord (w' : W) w'.2 1
    rw [h1, h1', congrArg (fun x : ↥J₀ => (x : W)) h]
  · show (ψ (w : W)).1 2 = (ψ (w' : W)).1 2
    have h1 : ((ψ (w : W)).1 1 : W) = ℓ (((ψ (w : W)).1 0 : ↥J₀) : W) := by
      simpa using hfixcoord (w : W) w.2 1
    have h1' : ((ψ (w' : W)).1 1 : W) = ℓ (((ψ (w' : W)).1 0 : ↥J₀) : W) := by
      simpa using hfixcoord (w' : W) w'.2 1
    have hcoord1 : (ψ (w : W)).1 1 = (ψ (w' : W)).1 1 := by
      apply Subtype.ext
      rw [h1, h1', congrArg (fun x : ↥J₀ => (x : W)) h]
    rw [(s1611e3_coords hW (ψ (w : W))).2.2, (s1611e3_coords hW (ψ (w' : W))).2.2, h,
      hcoord1]

private theorem s1611e3_coord_swap02 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {K L₀ : Subgroup (MulAut W)} {J₀ : Subgroup W}
    (s : ↥K ≃* Equiv.Perm (Fin 3)) (ψ : W ≃* ↥(s16c2m_Triples ↥J₀))
    (hs : ∀ (κ : ↥K) (w : W) (i : Fin 3),
      (ψ ((κ : MulAut W) w)).1 i = (ψ w).1 ((s κ)⁻¹ i))
    (hg : ∀ g ∈ L₀, ∀ (w : W) (i : Fin 3),
      (((ψ (g w)).1 i : ↥J₀) : W) = g (((ψ w).1 i : ↥J₀) : W))
    {κ ℓ : MulAut W} (hκ : κ ∈ K) (hσ : s ⟨κ, hκ⟩ = Equiv.swap 0 2) (hℓ : ℓ ∈ L₀) :
    Nat.card ↥(fixV (Subgroup.zpowers (κ * ℓ))) ≤ Nat.card ↥J₀ := by
  have hσinv : (s ⟨κ, hκ⟩)⁻¹ = Equiv.swap 0 2 := by rw [hσ]; decide
  have hfixcoord : ∀ w ∈ fixV (Subgroup.zpowers (κ * ℓ)), ∀ m : Fin 3,
      (((ψ w).1 m : ↥J₀) : W) = ℓ (((ψ w).1 (Equiv.swap 0 2 m) : ↥J₀) : W) := by
    intro w hw m
    have h1 := s1611e3_coord_action s ψ hs hg hκ hℓ w m
    rw [hσinv] at h1
    have h2 : (κ * ℓ) w = w := (mem_fixV.mp hw) (κ * ℓ) (Subgroup.mem_zpowers _)
    rwa [h2] at h1
  refine Nat.card_le_card_of_injective
    (fun w : ↥(fixV (Subgroup.zpowers (κ * ℓ))) => (ψ (w : W)).1 0) ?_
  intro w w' h
  beta_reduce at h
  apply Subtype.ext
  apply ψ.injective
  apply Subtype.ext
  funext m
  fin_cases m
  · apply Subtype.ext
    exact congrArg (fun x : ↥J₀ => (x : W)) h
  · apply Subtype.ext
    show ((ψ (w : W)).1 1 : W) = ((ψ (w' : W)).1 1 : W)
    have h1 : ((ψ (w : W)).1 2 : W) = ℓ (((ψ (w : W)).1 0 : ↥J₀) : W) := by
      simpa using hfixcoord (w : W) w.2 2
    have h1' : ((ψ (w' : W)).1 2 : W) = ℓ (((ψ (w' : W)).1 0 : ↥J₀) : W) := by
      simpa using hfixcoord (w' : W) w'.2 2
    rw [(s1611e3_coordsW hW (ψ (w : W))).2.1, (s1611e3_coordsW hW (ψ (w' : W))).2.1, h1,
      h1', congrArg (fun x : ↥J₀ => (x : W)) h]
  · apply Subtype.ext
    show ((ψ (w : W)).1 2 : W) = ((ψ (w' : W)).1 2 : W)
    have h1 : ((ψ (w : W)).1 2 : W) = ℓ (((ψ (w : W)).1 0 : ↥J₀) : W) := by
      simpa using hfixcoord (w : W) w.2 2
    have h1' : ((ψ (w' : W)).1 2 : W) = ℓ (((ψ (w' : W)).1 0 : ↥J₀) : W) := by
      simpa using hfixcoord (w' : W) w'.2 2
    rw [h1, h1', congrArg (fun x : ↥J₀ => (x : W)) h]

private theorem s1611e3_coord_swap12 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {K L₀ : Subgroup (MulAut W)} {J₀ : Subgroup W}
    (s : ↥K ≃* Equiv.Perm (Fin 3)) (ψ : W ≃* ↥(s16c2m_Triples ↥J₀))
    (hs : ∀ (κ : ↥K) (w : W) (i : Fin 3),
      (ψ ((κ : MulAut W) w)).1 i = (ψ w).1 ((s κ)⁻¹ i))
    (hg : ∀ g ∈ L₀, ∀ (w : W) (i : Fin 3),
      (((ψ (g w)).1 i : ↥J₀) : W) = g (((ψ w).1 i : ↥J₀) : W))
    {κ ℓ : MulAut W} (hκ : κ ∈ K) (hσ : s ⟨κ, hκ⟩ = Equiv.swap 1 2) (hℓ : ℓ ∈ L₀) :
    Nat.card ↥(fixV (Subgroup.zpowers (κ * ℓ))) ≤ Nat.card ↥J₀ := by
  have hσinv : (s ⟨κ, hκ⟩)⁻¹ = Equiv.swap 1 2 := by rw [hσ]; decide
  have hfixcoord : ∀ w ∈ fixV (Subgroup.zpowers (κ * ℓ)), ∀ m : Fin 3,
      (((ψ w).1 m : ↥J₀) : W) = ℓ (((ψ w).1 (Equiv.swap 1 2 m) : ↥J₀) : W) := by
    intro w hw m
    have h1 := s1611e3_coord_action s ψ hs hg hκ hℓ w m
    rw [hσinv] at h1
    have h2 : (κ * ℓ) w = w := (mem_fixV.mp hw) (κ * ℓ) (Subgroup.mem_zpowers _)
    rwa [h2] at h1
  refine Nat.card_le_card_of_injective
    (fun w : ↥(fixV (Subgroup.zpowers (κ * ℓ))) => (ψ (w : W)).1 2) ?_
  intro w w' h
  beta_reduce at h
  apply Subtype.ext
  apply ψ.injective
  apply Subtype.ext
  funext m
  fin_cases m
  · apply Subtype.ext
    show ((ψ (w : W)).1 0 : W) = ((ψ (w' : W)).1 0 : W)
    have h1 : ((ψ (w : W)).1 1 : W) = ℓ (((ψ (w : W)).1 2 : ↥J₀) : W) := by
      simpa using hfixcoord (w : W) w.2 1
    have h1' : ((ψ (w' : W)).1 1 : W) = ℓ (((ψ (w' : W)).1 2 : ↥J₀) : W) := by
      simpa using hfixcoord (w' : W) w'.2 1
    rw [(s1611e3_coordsW hW (ψ (w : W))).1, (s1611e3_coordsW hW (ψ (w' : W))).1, h1, h1',
      congrArg (fun x : ↥J₀ => (x : W)) h]
  · apply Subtype.ext
    show ((ψ (w : W)).1 1 : W) = ((ψ (w' : W)).1 1 : W)
    have h1 : ((ψ (w : W)).1 1 : W) = ℓ (((ψ (w : W)).1 2 : ↥J₀) : W) := by
      simpa using hfixcoord (w : W) w.2 1
    have h1' : ((ψ (w' : W)).1 1 : W) = ℓ (((ψ (w' : W)).1 2 : ↥J₀) : W) := by
      simpa using hfixcoord (w' : W) w'.2 1
    rw [h1, h1', congrArg (fun x : ↥J₀ => (x : W)) h]
  · apply Subtype.ext
    exact congrArg (fun x : ↥J₀ => (x : W)) h

section Certified


theorem s1611e3_v1_ln3_coord {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {X K L₀ : Subgroup (MulAut W)} {J₀ Z : Subgroup W} (hM : S16C11Model X K J₀)
    (hK : IsSym ↥K 3) (hdir : IsInternalDirect K L₀ X) (hL₀ : IsLn ↥L₀ 3 1)
    (hJ : ∀ x ∈ L₀, ∀ y ∈ J₀, x y ∈ J₀) (hN : BinaryNaturalSL L₀ J₀ Z 3 1)
    (hZ : Z ≤ fixV L₀) (hZne : Z ≠ ⊥) (hcomm : commSub J₀ L₀ = J₀) :
    (∀ t ∈ X, orderOf t = 2 → 3 ≤ rkIdx (fixV (Subgroup.zpowers t))) ∧
    (∀ E ∈ E3.aSet 2 X, rk ↥E ≤ 2) ∧ (∀ E ∈ E3.aSet 3 X, False) := by
  classical
  have hLX : L₀ ≤ X := hdir.2.2 ▸ le_sup_right
  have hKL : ∀ k ∈ K, ∀ l ∈ L₀, k * l = l * k := s16c11_comm_of_isInternalDirect hdir
  have hLK : ∀ l ∈ L₀, ∀ k ∈ K, l * k = k * l := fun l hl k hk => (hKL k hk l hl).symm
  let φ : ↥L₀ →* MulAut ↥J₀ := CFSG.Quasithin.H13.VolI.resHom L₀ J₀ hJ
  let H : Subgroup (MulAut ↥J₀) := φ.range
  have hinj : Function.Injective φ := s16c11_v1_resHom_injective hM hLX hLK hJ
  obtain ⟨K', hF, hFin, hcardK', hReal⟩ := hN
  have hZle : Z ≤ J₀ := by obtain ⟨π, hπ⟩ := hReal; exact hπ.2.1
  have hN' : BinaryNaturalSL H ⊤ (Z.subgroupOf J₀) 3 1 :=
    ⟨K', hF, hFin, hcardK',
      CFSG.Quasithin.H13.VolI.realizes_resHom_range hJ (FFModel.nat (StatedSL 3 K')) hReal⟩
  obtain ⟨D'⟩ := hN'.toL3Coord
  have hJ2 : ∀ x : ↥J₀, x ^ 2 = 1 := fun x => Subtype.ext (by simpa [pow_two] using hW (x : W))
  have hZ' : Z.subgroupOf J₀ ≤ fixV H :=
    CFSG.Quasithin.H13.VolI.subgroupOf_le_fixV_resHom_range (L := L₀) (U := J₀) hJ hZ
  have hfixH : fixV H = Z.subgroupOf J₀ := by
    refine le_antisymm ?_ hZ'
    intro v hv
    have hβ1 : D'.β ⟨v, Subgroup.mem_top v⟩ = 1 := by
      have hfixθ : ∀ γ : L3.Γ,
          L3.act γ (Multiplicative.toAdd (D'.β ⟨v, Subgroup.mem_top v⟩)) =
            Multiplicative.toAdd (D'.β ⟨v, Subgroup.mem_top v⟩) := by
        intro γ
        have hπv : (D'.π γ : MulAut ↥J₀) v = v := hv _ (D'.π γ).2
        have h1 := D'.equi γ ⟨v, Subgroup.mem_top v⟩ (Subgroup.mem_top _)
        rw [hπv] at h1
        exact (congrArg Multiplicative.toAdd h1).symm
      by_contra h0
      obtain ⟨γ, hγ⟩ := L3.act_nofix
        (Multiplicative.toAdd (D'.β ⟨v, Subgroup.mem_top v⟩)) (by simpa using h0)
      exact hγ (hfixθ γ)
    exact (D'.ker_β ⟨v, Subgroup.mem_top v⟩).1 hβ1
  have hZ'ne : Z.subgroupOf J₀ ≠ ⊥ := by
    intro hbot
    apply hZne
    have hcard : Nat.card ↥(Z.subgroupOf J₀) = Nat.card ↥Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv
    rw [hbot, Subgroup.card_bot] at hcard
    exact (Subgroup.card_eq_one).1 hcard.symm
  have hcommH : commSub (⊤ : Subgroup ↥J₀) H = ⊤ := by
    have hcommX : XMod.commOf ↥L₀ J₀ = J₀ := by
      rw [CFSG.Quasithin.commOf_eq_commSub]; exact hcomm
    rw [← commV_eq_commSub H]
    exact CFSG.Quasithin.H13.VolI.commV_resHom_range (L := L₀) (U := J₀) hJ hcommX
  have hZcard : Nat.card ↥(Z.subgroupOf J₀) = 2 := by
    have hle : Nat.card ↥(Z.subgroupOf J₀) ≤ 2 := by
      have hnat : BinaryNaturalSL H ⊤ (⊤ ⊓ fixV H) 3 1 := by
        rw [top_inf_eq, hfixH]; exact hN'
      have hcommH' : XMod.commOf ↥H (⊤ : Subgroup ↥J₀) = ⊤ := by
        rw [CFSG.Quasithin.commOf_eq_commSub]; exact hcommH
      have h1 := card_fixV_le_two_of_natural3 hJ2 H ⊤ D'.inv_U hcommH' hnat
      rwa [top_inf_eq, hfixH] at h1
    have hge : 2 ≤ Nat.card ↥(Z.subgroupOf J₀) := by
      have h1 : 1 < Nat.card ↥(Z.subgroupOf J₀) :=
        (Subgroup.one_lt_card_iff_ne_bot _).2 hZ'ne
      omega
    omega
  have hcardJ : Nat.card ↥J₀ = 16 := by
    have h := D'.card_U
    rw [Subgroup.card_top, hZcard] at h
    norm_num at h
    exact h
  have hrkJ : rk ↥J₀ = 4 := by
    unfold rk
    rw [hcardJ, show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat.prime_pow]
  obtain ⟨hJ', Θ, hΘ⟩ := s16c11_v1_model_pair hM hLX hLK
  have hJeq : hJ' = hJ := Subsingleton.elim _ _
  rw [hJeq] at hΘ
  obtain ⟨s, ψ, hs, hg⟩ := hM
  have hgL : ∀ g ∈ L₀, ∀ (w : W) (i : Fin 3),
      (((ψ (g w)).1 i : ↥J₀) : W) = g (((ψ w).1 i : ↥J₀) : W) :=
    fun g hg' w i => hg g (hLX hg') (fun k hk => (hKL k hk g hg').symm) w i
  have hcardW : Nat.card W = 256 := by
    have h1 : Nat.card W = Nat.card ↥(s16c2m_Triples ↥J₀) := Nat.card_congr ψ.toEquiv
    rw [h1, s16c2m_card_Triples, hcardJ]
    norm_num
  have hrkW : rk W = 8 := by
    change padicValNat 2 (Nat.card W) = 8
    rw [hcardW, show (256 : ℕ) = 2 ^ 8 by norm_num, padicValNat.prime_pow]
  have hle_of_card : ∀ u : MulAut W, Nat.card ↥(fixV (Subgroup.zpowers u)) ≤ 16 →
      3 ≤ rkIdx (fixV (Subgroup.zpowers u)) := by
    intro u hu
    have hrf : rk ↥(fixV (Subgroup.zpowers u)) ≤ 4 := by
      have hc := card_eq_two_pow hW (fixV (Subgroup.zpowers u))
      have h2 : 2 ^ rk ↥(fixV (Subgroup.zpowers u)) ≤ 2 ^ 4 := by
        rw [← hc]; simpa using hu
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
    have hsum := rk_add_rkIdx (H := fixV (Subgroup.zpowers u))
    omega
  have hcardC : ∀ (ℓ : MulAut W) (hℓ : ℓ ∈ L₀), ℓ * ℓ = 1 → ℓ ≠ 1 →
      Nat.card ↥(fixV (Subgroup.zpowers (φ ⟨ℓ, hℓ⟩))) ≤ 4 := by
    intro ℓ hℓ hℓ2 hℓ1
    have hφ1 : φ ⟨ℓ, hℓ⟩ ≠ 1 := by
      intro h
      apply hℓ1
      exact congrArg Subtype.val (hinj (h.trans (map_one φ).symm))
    have hφ2 : φ ⟨ℓ, hℓ⟩ * φ ⟨ℓ, hℓ⟩ = 1 := by
      have h : (⟨ℓ, hℓ⟩ : ↥L₀) * ⟨ℓ, hℓ⟩ = 1 := Subtype.ext hℓ2
      calc φ ⟨ℓ, hℓ⟩ * φ ⟨ℓ, hℓ⟩ = φ ((⟨ℓ, hℓ⟩ : ↥L₀) * ⟨ℓ, hℓ⟩) := (map_mul φ _ _).symm
        _ = φ 1 := by rw [h]
        _ = 1 := map_one φ
    have hcr := s1611e3_v1_ln3_comm_rank hJ2 hN' hZ' hcommH hZ'ne
      (s := φ ⟨ℓ, hℓ⟩) ((MonoidHom.mem_range).mpr ⟨⟨ℓ, hℓ⟩, rfl⟩) hφ1 hφ2
    have hdu : rkIdx (fixV (Subgroup.zpowers (φ ⟨ℓ, hℓ⟩))) =
        rk ↥(commSub (⊤ : Subgroup ↥J₀) (Subgroup.zpowers (φ ⟨ℓ, hℓ⟩))) := by
      rw [CFSG.Quasithin.rkIdx_fixV_zpowers (φ ⟨ℓ, hℓ⟩), CFSG.Quasithin.commV_eq_commSub]
    have hsum : rk ↥(fixV (Subgroup.zpowers (φ ⟨ℓ, hℓ⟩))) +
        rk ↥(commSub (⊤ : Subgroup ↥J₀) (Subgroup.zpowers (φ ⟨ℓ, hℓ⟩))) = 4 := by
      have h := rk_add_rkIdx (H := fixV (Subgroup.zpowers (φ ⟨ℓ, hℓ⟩)))
      rw [hdu, hrkJ] at h
      exact h
    have hrf : rk ↥(fixV (Subgroup.zpowers (φ ⟨ℓ, hℓ⟩))) ≤ 2 := by omega
    calc Nat.card ↥(fixV (Subgroup.zpowers (φ ⟨ℓ, hℓ⟩)))
        = 2 ^ rk ↥(fixV (Subgroup.zpowers (φ ⟨ℓ, hℓ⟩))) := card_eq_two_pow hJ2 _
      _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hrf
      _ = 4 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro t htX htord
    have ht2 : t * t = 1 := by
      rw [← pow_two, ← htord]; exact pow_orderOf_eq_one t
    have ht1 : t ≠ 1 := by
      intro h
      rw [h, orderOf_one] at htord
      omega
    obtain ⟨κ, hκK, ℓ, hℓL, hκℓ⟩ := s16c2m_exists_mul_of_mem_sup hKL (hdir.2.2.symm ▸ htX)
    have hκℓ_comm : Commute κ ℓ := hKL κ hκK ℓ hℓL
    have ht2' : t ^ 2 = 1 := by rwa [pow_two]
    have hκ2p : κ ^ 2 = 1 := by
      have h1 : κ ^ 2 * ℓ ^ 2 = 1 := by
        rw [← hκℓ_comm.mul_pow 2, hκℓ, ht2']
      have h2 : κ ^ 2 = (ℓ ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hmemL : κ ^ 2 ∈ L₀ := by rw [h2]; exact L₀.inv_mem (L₀.pow_mem hℓL 2)
      have hmem : κ ^ 2 ∈ K ⊓ L₀ := ⟨K.pow_mem hκK 2, hmemL⟩
      rwa [hdir.2.1, Subgroup.mem_bot] at hmem
    have hℓ2p : ℓ ^ 2 = 1 := by
      have h1 : κ ^ 2 * ℓ ^ 2 = 1 := by
        rw [← hκℓ_comm.mul_pow 2, hκℓ, ht2']
      rwa [hκ2p, one_mul] at h1
    have hκ2 : κ * κ = 1 := by rwa [pow_two] at hκ2p
    have hℓ2 : ℓ * ℓ = 1 := by rw [← pow_two]; exact hℓ2p
    by_cases hκ1 : κ = 1
    · have htℓ : t = ℓ := by rw [← hκℓ, hκ1, one_mul]
      have hℓ1 : ℓ ≠ 1 := by rw [← htℓ]; exact ht1
      rw [htℓ]
      apply hle_of_card
      have hfixprod := s1611e3_fixV_prod_map φ Θ hΘ (Subgroup.zpowers ℓ)
        (Subgroup.zpowers_le.2 hℓL)
      have hmapz : ((Subgroup.zpowers ℓ).subgroupOf L₀).map φ =
          Subgroup.zpowers (φ ⟨ℓ, hℓL⟩) := s1611e3_map_zpowers_subgroupOf φ ℓ hℓL
      rw [hfixprod, Subgroup.card_map_of_injective (f := (Θ : ↥J₀ × ↥J₀ →* W)) Θ.injective,
        hmapz, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
      calc Nat.card ↥(fixV (Subgroup.zpowers (φ ⟨ℓ, hℓL⟩))) *
            Nat.card ↥(fixV (Subgroup.zpowers (φ ⟨ℓ, hℓL⟩)))
          ≤ 4 * 4 := Nat.mul_le_mul (hcardC ℓ hℓL hℓ2 hℓ1) (hcardC ℓ hℓL hℓ2 hℓ1)
        _ = 16 := by norm_num
    · have hσ2 : s ⟨κ, hκK⟩ * s ⟨κ, hκK⟩ = 1 := by
        have h : (⟨κ, hκK⟩ : ↥K) * ⟨κ, hκK⟩ = 1 := Subtype.ext hκ2
        calc s ⟨κ, hκK⟩ * s ⟨κ, hκK⟩ = s ((⟨κ, hκK⟩ : ↥K) * ⟨κ, hκK⟩) := (map_mul s _ _).symm
          _ = s 1 := by rw [h]
          _ = 1 := map_one s
      have hσ1 : s ⟨κ, hκK⟩ ≠ 1 := by
        intro h
        apply hκ1
        exact congrArg Subtype.val (s.injective (h.trans (map_one s).symm))
      rw [← hκℓ]
      rcases s1611e3_perm3_involution (s ⟨κ, hκK⟩) hσ2 hσ1 with hσ | hσ | hσ
      · apply hle_of_card
        have hle := s1611e3_coord_swap01 hW s ψ hs hgL hκK hσ hℓL
        rwa [hcardJ] at hle
      · apply hle_of_card
        have hle := s1611e3_coord_swap02 hW s ψ hs hgL hκK hσ hℓL
        rwa [hcardJ] at hle
      · apply hle_of_card
        have hle := s1611e3_coord_swap12 hW s ψ hs hgL hκK hσ hℓL
        rwa [hcardJ] at hle
  · intro E hE
    exact s1611e3_rk_le_two_of_aSet_two hW hK hdir hL₀ hE
  · intro E hE3
    have hE2 : E ∈ E3.aSet 2 X :=
      ⟨hE3.1, hE3.2.1, hE3.2.2.1,
        fun B hB hmq => hE3.2.2.2 B hB (lt_trans hmq (by norm_num))⟩
    have hrk : rk ↥E ≤ 2 := s1611e3_rk_le_two_of_aSet_two hW hK hdir hL₀ hE2
    have hmq : E3.mQuot E ⊥ < 3 := by
      rw [E3.mQuot_bot_eq_rk]; omega
    have hfix := hE3.2.2.2 ⊥ bot_le hmq
    rw [B1.fixV_bot] at hfix
    exact hE3.2.1 (B1.eq_bot_of_fixV_eq_top hfix.symm)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
