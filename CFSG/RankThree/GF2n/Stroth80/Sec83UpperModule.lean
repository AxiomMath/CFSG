module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SecMod
public import CFSG.RankThree.GF2n.Stroth80.Sec5Comm
public import CFSG.RankThree.GF2n.Stroth80.Sec83Additive

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_comm_endo (hc : Ctx M Q Z B) {R : Subgroup G} (hRM : R ≤ M) {Md : Type}
    [AddCommGroup Md] [DistribMulAction ↥R Md] {κ : ↥Q →* Multiplicative Md}
    (hκ : IsSecMod R Q Z Md κ) {s : G} (hsM : s ∈ M) (hsR : ∀ ρ ∈ R, ⁅ρ⁻¹, s⁆ ∈ Q) :
    ∃ ε : Md →+ Md,
      (∀ x : ↥Q, ε (Multiplicative.toAdd (κ x)) =
        Multiplicative.toAdd (κ ⟨⁅(x : G), s⁆, hc.comm_mem_Q hsM x.2⟩)) ∧
      ∀ (z : ↥R) (a : Md), ε (z • a) = z • ε a := by
  have hP : ∀ r ∈ R, ∀ x ∈ Q, r * x * r⁻¹ ∈ Q := fun r hr x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hRM hr)) x).mp hx
  obtain ⟨c, hc'⟩ : ∃ c : ↥Q → ↥Q, ∀ x : ↥Q, (c x : G) = ⁅(x : G), s⁆ :=
    ⟨fun x => ⟨⁅(x : G), s⁆, hc.comm_mem_Q hsM x.2⟩, fun x => rfl⟩
  have hc'' : ∀ x : ↥Q, c x = ⟨⁅(x : G), s⁆, hc.comm_mem_Q hsM x.2⟩ :=
    fun x => Subtype.ext (hc' x)
  have hc_one : c 1 = 1 := Subtype.ext (by rw [hc']; simp)
  have hc_mul : ∀ x y : ↥Q, κ (c (x * y)) = κ (c x) * κ (c y) := fun x y => by
    rw [← map_mul, hκ.eq_iff, Subgroup.coe_mul, hc', hc', hc']
    exact hc.comm_mul_mem_Z hsM x.2 y.2
  let ε₀ : ↥Q →* Multiplicative Md :=
    { toFun := fun x => κ (c x)
      map_one' := by rw [hc_one, map_one]
      map_mul' := hc_mul }
  have hε₀Z : ∀ x : ↥Q, (x : G) ∈ Z → ε₀ x = 1 := fun x hx => by
    refine (hκ.ker (c x)).mpr ?_
    rw [hc']
    have h1 : s * (x : G)⁻¹ * s⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hsM) _).mp (Z.inv_mem hx)
    rw [show ⁅(x : G), s⁆ = (x : G) * (s * (x : G)⁻¹ * s⁻¹) by rw [commutatorElement_def]; group]
    exact Z.mul_mem hx h1
  have hker : κ.ker ≤ ε₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    exact hε₀Z x ((hκ.ker x).mp hx)
  let ε' : Multiplicative Md →* Multiplicative Md :=
    κ.liftOfRightInverse (Function.surjInv hκ.surj) (Function.rightInverse_surjInv hκ.surj)
      ⟨ε₀, hker⟩
  have hε' : ∀ x : ↥Q, ε' (κ x) = κ (c x) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply κ _ _ ⟨ε₀, hker⟩ x
  let ε : Md →+ Md :=
    { toFun := fun a => Multiplicative.toAdd (ε' (Multiplicative.ofAdd a))
      map_zero' := by simp
      map_add' := fun a b => by simp [ofAdd_add, toAdd_mul] }
  have hεκ : ∀ x : ↥Q, ε (Multiplicative.toAdd (κ x)) = Multiplicative.toAdd (κ (c x)) := by
    intro x
    show Multiplicative.toAdd (ε' (Multiplicative.ofAdd (Multiplicative.toAdd (κ x)))) = _
    rw [ofAdd_toAdd, hε']
  refine ⟨ε, fun x => by rw [hεκ, hc''], ?_⟩
  intro z a
  obtain ⟨x, hx⟩ := hκ.surj (Multiplicative.ofAdd a)
  have hxa : Multiplicative.toAdd (κ x) = a := by rw [hx]; rfl
  subst hxa
  obtain ⟨y, hy⟩ : ∃ y : ↥Q, (y : G) = (z : G) * (x : G) * (z : G)⁻¹ :=
    ⟨⟨_, hP z z.2 x x.2⟩, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ↥Q, (w : G) = (z : G) * (c x : G) * (z : G)⁻¹ :=
    ⟨⟨_, hP z z.2 (c x) (c x).2⟩, rfl⟩
  have hy1 : κ y = Multiplicative.ofAdd (z • Multiplicative.toAdd (κ x)) :=
    hκ.act z x y hy
  have hw1 : κ w = Multiplicative.ofAdd (z • Multiplicative.toAdd (κ (c x))) :=
    hκ.act z (c x) w hw
  have hyw : κ (c y) = κ w := by
    rw [hκ.eq_iff, hc', hw, hy, hc']
    exact hc.comm_conj_mem_Z hsM (hRM z.2) (hsR z z.2) x.2
  have hy2 : Multiplicative.toAdd (κ y) = z • Multiplicative.toAdd (κ x) := by
    rw [hy1, toAdd_ofAdd]
  have hw2 : Multiplicative.toAdd (κ w) = z • Multiplicative.toAdd (κ (c x)) := by
    rw [hw1, toAdd_ofAdd]
  rw [← hy2, hεκ y, hyw, hw2, hεκ x]

section Module

variable {R : Type*} [Group R] {Md : Type*} [AddCommGroup Md] [Finite Md] [DistribMulAction R Md]

theorem eps_kills_sW1 (ε : Md →+ Md) (hεR : ∀ (z : R) (a : Md), ε (z • a) = z • ε a)
    {sV sV1 sW1 sA1 sA2 F₁ F₂ : AddSubgroup Md} {L₁ L₂ : Subgroup R} {q : ℕ}
    (hV1 : ∀ a ∈ sV1, ε a = 0)
    (hA1 : ∀ a ∈ sA1, ∀ l ∈ L₁, l • a - a ∈ sV1)
    (hA2 : ∀ a ∈ sA2, ∀ l ∈ L₂, l • a - a ∈ sV1) (hW1 : sW1 = sA1 ⊔ sA2)
    (hF₁ : ∀ b : Md, (∀ l ∈ L₁, l • b = b) → b ∈ F₁)
    (hF₂ : ∀ b : Md, (∀ l ∈ L₂, l • b = b) → b ∈ F₂) (hFV₁ : F₁ ≤ sV) (hFV₂ : F₂ ≤ sV)
    (hc₁ : Nat.card F₁ ≤ q) (hc₂ : Nat.card F₂ ≤ q)
    (hirr : ∀ T : AddSubgroup Md, T ≤ sV → (∀ (z : R), ∀ a ∈ T, z • a ∈ T) → T = ⊥ ∨ T = sV)
    (hsV : q * q < Nat.card sV) (hinv : ∀ (z : R), ∀ a ∈ sW1, z • a ∈ sW1) :
    ∀ a ∈ sW1, ε a = 0 := by
  have hfix : ∀ (A : AddSubgroup Md) (L : Subgroup R) (F : AddSubgroup Md),
      (∀ a ∈ A, ∀ l ∈ L, l • a - a ∈ sV1) → (∀ b : Md, (∀ l ∈ L, l • b = b) → b ∈ F) →
      ∀ a ∈ A, ε a ∈ F := by
    intro A L F hA hF a ha
    refine hF _ fun l hl => ?_
    have h1 : l • ε a = ε (l • a) := (hεR l a).symm
    have h2 : ε (l • a) = ε a := by
      have := hV1 _ (hA a ha l hl)
      rw [map_sub, sub_eq_zero] at this
      exact this
    rw [h1, h2]
  have hT : sW1.map ε ≤ F₁ ⊔ F₂ := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hW1] at ha
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := AddSubgroup.mem_sup.mp ha
    rw [map_add]
    exact AddSubgroup.add_mem_sup (hfix sA1 L₁ F₁ hA1 hF₁ a₁ ha₁) (hfix sA2 L₂ F₂ hA2 hF₂ a₂ ha₂)
  have hcard : Nat.card ↥(sW1.map ε) ≤ q * q := by
    have h1 : Nat.card ↥(sW1.map ε) ≤ Nat.card ↥(F₁ ⊔ F₂) := Nat.card_mono (Set.toFinite _) hT
    have h2 := card_sup_mul_card_inf_addSubgroup F₁ F₂
    have h3 : Nat.card ↥(F₁ ⊔ F₂) ≤ Nat.card ↥(F₁ ⊔ F₂) * Nat.card ↥(F₁ ⊓ F₂) :=
      Nat.le_mul_of_pos_right _ Nat.card_pos
    rw [h2] at h3
    exact h1.trans (h3.trans (Nat.mul_le_mul hc₁ hc₂))
  have hTV : sW1.map ε ≤ sV := hT.trans (sup_le hFV₁ hFV₂)
  have hTinv : ∀ (z : R), ∀ a ∈ sW1.map ε, z • a ∈ sW1.map ε := by
    rintro z _ ⟨a, ha, rfl⟩
    exact ⟨z • a, hinv z a ha, hεR z a⟩
  rcases hirr _ hTV hTinv with h | h
  · intro a ha
    have : ε a ∈ sW1.map ε := ⟨a, ha, rfl⟩
    rw [h, AddSubgroup.mem_bot] at this
    exact this
  · exfalso
    rw [h] at hcard
    omega

theorem eps_kills_sW (ε : Md →+ Md) (hεR : ∀ (z : R) (a : Md), ε (z • a) = z • ε a)
    {sV sW1 sW F₁ : AddSubgroup Md} {L₁ : Subgroup R} {q : ℕ}
    (hW1 : ∀ a ∈ sW1, ε a = 0) (hW : ∀ a ∈ sW, ∀ l ∈ L₁, l • a - a ∈ sW1)
    (hF₁ : ∀ b : Md, (∀ l ∈ L₁, l • b = b) → b ∈ F₁) (hFV₁ : F₁ ≤ sV) (hc₁ : Nat.card F₁ ≤ q)
    (hirr : ∀ T : AddSubgroup Md, T ≤ sV → (∀ (z : R), ∀ a ∈ T, z • a ∈ T) → T = ⊥ ∨ T = sV)
    (hsV : q < Nat.card sV) (hinv : ∀ (z : R), ∀ a ∈ sW, z • a ∈ sW) :
    ∀ a ∈ sW, ε a = 0 := by
  have hfix : ∀ a ∈ sW, ε a ∈ F₁ := by
    intro a ha
    refine hF₁ _ fun l hl => ?_
    have h1 : l • ε a = ε (l • a) := (hεR l a).symm
    have h2 : ε (l • a) = ε a := by
      have := hW1 _ (hW a ha l hl)
      rw [map_sub, sub_eq_zero] at this
      exact this
    rw [h1, h2]
  have hT : sW.map ε ≤ F₁ := by
    rintro _ ⟨a, ha, rfl⟩
    exact hfix a ha
  have hcard : Nat.card ↥(sW.map ε) ≤ q :=
    (Nat.card_mono (Set.toFinite _) hT).trans hc₁
  have hTinv : ∀ (z : R), ∀ a ∈ sW.map ε, z • a ∈ sW.map ε := by
    rintro z _ ⟨a, ha, rfl⟩
    exact ⟨z • a, hinv z a ha, hεR z a⟩
  rcases hirr _ (hT.trans hFV₁) hTinv with h | h
  · intro a ha
    have : ε a ∈ sW.map ε := ⟨a, ha, rfl⟩
    rw [h, AddSubgroup.mem_bot] at this
    exact this
  · exfalso
    rw [h] at hcard
    omega

end Module

section Section

variable {R P I V : Subgroup G} {Md : Type} [AddCommGroup Md] [DistribMulAction ↥R Md]
  {κ : ↥P →* Multiplicative Md}

theorem smul_toAdd_sub_eq (hκ : IsSecMod R P I Md κ) (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P)
    (l : ↥R) (x : ↥P) (hc : ⁅(l : G), (x : G)⁆ ∈ P) :
    l • Multiplicative.toAdd (κ x) - Multiplicative.toAdd (κ x) =
      Multiplicative.toAdd (κ ⟨⁅(l : G), (x : G)⁆, hc⟩) := by
  have h1 := hκ.act l x ⟨(l : G) * x * (l : G)⁻¹, hP l l.2 x x.2⟩ rfl
  have h2 : (⟨(l : G) * x * (l : G)⁻¹, hP l l.2 x x.2⟩ : ↥P) = ⟨⁅(l : G), (x : G)⁆, hc⟩ * x :=
    Subtype.ext (by simp [commutatorElement_def])
  rw [h2, map_mul] at h1
  have h3 : Multiplicative.toAdd (κ ⟨⁅(l : G), (x : G)⁆, hc⟩ * κ x) =
      l • Multiplicative.toAdd (κ x) := by rw [h1, toAdd_ofAdd]
  rw [toAdd_mul] at h3
  rw [← h3]
  abel

theorem conj_mem_of_secSub_invariant (hκ : IsSecMod R P I Md κ)
    (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P) {U : Subgroup G} (hIU : I ≤ U) (hUP : U ≤ P)
    (hinv : ∀ z : ↥R, ∀ a ∈ secSub κ U, z • a ∈ secSub κ U) :
    ∀ r ∈ R, ∀ u ∈ U, r * u * r⁻¹ ∈ U := by
  intro r hr u hu
  have hu1 : Multiplicative.toAdd (κ ⟨u, hUP hu⟩) ∈ secSub κ U := mem_secSub.mpr ⟨_, hu, rfl⟩
  have h2 := hinv ⟨r, hr⟩ _ hu1
  have h3 := hκ.act ⟨r, hr⟩ ⟨u, hUP hu⟩ ⟨r * u * r⁻¹, hP r hr u (hUP hu)⟩ rfl
  have h3' : Multiplicative.toAdd (κ ⟨r * u * r⁻¹, hP r hr u (hUP hu)⟩) =
      (⟨r, hr⟩ : ↥R) • Multiplicative.toAdd (κ ⟨u, hUP hu⟩) := by
    rw [h3, toAdd_ofAdd]
  have h4 : Multiplicative.toAdd (κ ⟨r * u * r⁻¹, hP r hr u (hUP hu)⟩) ∈ secSub κ U := by
    rw [h3']
    exact h2
  exact (toAdd_mem_secSub_iff hκ hIU _).mp h4

theorem secSub_irred_of_irred (hκ : IsSecMod R P I Md κ) (hIV : I ≤ V) (hVP : V ≤ P)
    (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P)
    (hirr : ∀ U : Subgroup G, I ≤ U → U ≤ V → (∀ r ∈ R, ∀ u ∈ U, r * u * r⁻¹ ∈ U) →
      U = I ∨ U = V) :
    ∀ T : AddSubgroup Md, T ≤ secSub κ V → (∀ z : ↥R, ∀ a ∈ T, z • a ∈ T) →
      T = ⊥ ∨ T = secSub κ V := by
  intro T hTV hTinv
  obtain ⟨U, hIU, hUP, hUT⟩ := exists_secSub_eq (hIV.trans hVP) hκ T
  have hUV : U ≤ V := (secSub_le_secSub_iff hκ hUP hIV).mp (hUT ▸ hTV)
  have hRU : ∀ r ∈ R, ∀ u ∈ U, r * u * r⁻¹ ∈ U :=
    conj_mem_of_secSub_invariant hκ hP hIU hUP (hUT ▸ hTinv)
  rcases hirr U hIU hUV hRU with h | h
  · left
    rw [← hUT, h, secSub_eq_bot hκ]
  · right
    rw [← hUT, h]

theorem commutator_zpowers_le {Q U : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (U : Set G)) (hsU : ∀ x ∈ Q, ⁅x, s⁆ ∈ U) :
    ⁅Q, Subgroup.zpowers s⁆ ≤ U := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have key : y ∈ Subgroup.normalizer (U : Set G) ∧ ∀ x ∈ Q, ⁅x, y⁆ ∈ U := by
    rw [Subgroup.zpowers_eq_closure] at hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨hs, hsU⟩
    | one => exact ⟨Subgroup.one_mem _, fun x _ => by simp [commutatorElement_def]⟩
    | mul y y' _ _ hy hy' =>
      refine ⟨Subgroup.mul_mem _ hy.1 hy'.1, fun x hx => ?_⟩
      have e : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact U.mul_mem (hy.2 x hx) ((Subgroup.mem_normalizer_iff.mp hy.1 _).mp (hy'.2 x hx))
    | inv y _ hy =>
      refine ⟨Subgroup.inv_mem _ hy.1, fun x hx => ?_⟩
      have e : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy.1) _).mp (U.inv_mem (hy.2 x hx))
  exact key.2 x hx

end Section

end CFSG.RankThree.GF2n.Stroth80
