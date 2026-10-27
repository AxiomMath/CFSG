module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

section Structure

variable {W : Type} [CommGroup W] [Finite W] {X H : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}

private theorem s16e_twoB_perm3_transitive {α : Type} [Finite α] (hα : Nat.card α = 3)
    {σ : Equiv.Perm α} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) (a b : α) :
    ∃ m : ℕ, (σ ^ m) a = b := by
  obtain e : α ≃ Fin 3 := Finite.equivFinOfCardEq hα
  have key : ∀ τ : Equiv.Perm (Fin 3), τ ^ 3 = 1 → τ ≠ 1 →
      ∀ a b : Fin 3, ∃ m : Fin 3, (τ ^ (m : ℕ)) a = b := by decide
  have h3' : (Equiv.permCongrHom e σ) ^ 3 = 1 := by
    rw [← map_pow, h3, map_one]
  have h1' : Equiv.permCongrHom e σ ≠ 1 := by
    intro h
    exact h1 ((Equiv.permCongrHom e).injective (by rw [h, map_one]))
  obtain ⟨m, hm⟩ := key _ h3' h1' (e a) (e b)
  refine ⟨m, ?_⟩
  have h2 : ((Equiv.permCongrHom e σ) ^ (m : ℕ)) (e a) = e ((σ ^ (m : ℕ)) a) := by
    rw [← map_pow]
    simp [Equiv.permCongrHom]
  rw [h2] at hm
  exact e.injective hm

private theorem s16e_twoB_orbit_dvd {G α : Type} [Group G] [Finite G] (f : G →* Equiv.Perm α)
    (a : α) : (Set.range fun g : G => f g a).ncard ∣ Nat.card G := by
  letI : MulAction G α := MulAction.compHom α f
  have h1 : Set.range (fun g : G => f g a) = MulAction.orbit G a := by
    ext x
    simp only [Set.mem_range, MulAction.mem_orbit_iff]
    rfl
  rw [h1, ← MulAction.index_stabilizer G a]
  exact (MulAction.stabilizer G a).index_dvd_card

private theorem s16e_twoB_dvd_perm {G α : Type} [Group G] [Finite G] [Finite α]
    (f : G →* Equiv.Perm α) (hf : Function.Injective f) (hle : Nat.card α ≤ 3)
    (h3 : 3 ∣ Nat.card G) : Nat.card α = 3 ∧ ∀ a b : α, ∃ g : G, f g a = b := by
  have hdvd : Nat.card G ∣ (Nat.card α).factorial := by
    have := Subgroup.card_dvd_of_injective f hf
    rwa [Nat.card_perm] at this
  have h3le : 3 ≤ Nat.card α := (Nat.Prime.dvd_factorial Nat.prime_three).1 (h3.trans hdvd)
  have hα : Nat.card α = 3 := le_antisymm hle h3le
  refine ⟨hα, fun a b => ?_⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg
    omega
  have hσ3 : (f g) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
  have hσ1 : f g ≠ 1 := fun h => hg1 (hf (by rw [h, map_one]))
  obtain ⟨m, hm⟩ := s16e_twoB_perm3_transitive hα hσ3 hσ1 a b
  exact ⟨g ^ m, by rw [map_pow]; exact hm⟩

private theorem s16e_twoB_three_le_ncard {α : Type} [Finite α] {S : Set α} {x y z : α}
    (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    3 ≤ S.ncard := by
  have h : ({x, y, z} : Set α) ⊆ S := by
    intro w hw
    rcases hw with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  have h3 : ({x, y, z} : Set α).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  exact h3 ▸ Set.ncard_le_ncard h (Set.toFinite S)

theorem s16e_two_le_fixIrr (hHX : H ≤ X) : H ≤ s16e_two_fixIrr X H := by
  intro h hh
  refine ⟨hHX hh, fun I hI => ?_⟩
  obtain ⟨-, hirr⟩ := hI
  obtain ⟨-, hstab, -, -⟩ := hirr
  apply le_antisymm
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
    exact hstab h hh u hu
  · intro u hu
    refine Subgroup.mem_map.2 ⟨h⁻¹ u, hstab h⁻¹ (H.inv_mem hh) u hu, ?_⟩
    simp

theorem s16e_two_cent_inf_fixIrr (F : Cfg2Setting X H J₀ J₁)
    (hE₀ : Z391.EndUnitsTrivial H J₀) (hE₁ : Z391.EndUnitsTrivial H J₁) :
    s16e_two_cent X H ⊓ s16e_two_fixIrr X H = ⊥ := by
  rw [eq_bot_iff]
  intro k hk
  obtain ⟨hkK, hkN⟩ := hk
  obtain ⟨-, hkfix⟩ := hkN
  have hc : k ∈ Subgroup.centralizer (H : Set (MulAut W)) := (Subgroup.mem_inf.1 hkK).2
  have := s16e_two_eq_one_of_fixes F hE₀ hE₁ hc (hkfix J₀ F.irr₀) (hkfix J₁ F.irr₁)
  rw [Subgroup.mem_bot]
  exact this

theorem s16e_two_commutator_cent_fixIrr (F : Cfg2Setting X H J₀ J₁)
    (hE₀ : Z391.EndUnitsTrivial H J₀) (hE₁ : Z391.EndUnitsTrivial H J₁) :
    ⁅s16e_two_cent X H, s16e_two_fixIrr X H⁆ = ⊥ := by
  have hKN := s16e_two_cent_inf_fixIrr F hE₀ hE₁
  have hdisj : Disjoint ((s16e_two_conjAut F).ker) ((s16e_two_irrAct F).ker) := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx1' : x ∈ (s16e_two_conjAut F).ker := hx1
    rw [s16e_two_conjAut_ker, Subgroup.mem_subgroupOf] at hx1'
    have hx2' : (x : MulAut W) ∈ s16e_two_fixIrr X H := by
      refine ⟨x.2, fun I hI => ?_⟩
      have h1 := congrArg (fun σ : Equiv.Perm ↥(irrSet H) => (σ ⟨I, hI⟩ : Subgroup W))
        (MonoidHom.mem_ker.1 hx2)
      simpa [s16e_two_irrAct_apply] using h1
    have : (x : MulAut W) ∈ s16e_two_cent X H ⊓ s16e_two_fixIrr X H := ⟨hx1', hx2'⟩
    rw [hKN, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro k hk n hn
  have hkX : k ∈ X := (Subgroup.mem_inf.1 hk).1
  have hnX : n ∈ X := hn.1
  have hk' : (⟨k, hkX⟩ : ↥X) ∈ (s16e_two_conjAut F).ker := by
    rw [s16e_two_conjAut_ker, Subgroup.mem_subgroupOf]
    exact hk
  have hn' : (⟨n, hnX⟩ : ↥X) ∈ (s16e_two_irrAct F).ker := by
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro I
    apply Subtype.ext
    simpa [s16e_two_irrAct_apply] using hn.2 I I.2
  have hc := Subgroup.commute_of_normal_of_disjoint _ _ (MonoidHom.normal_ker _)
    (MonoidHom.normal_ker _) hdisj _ _ hk' hn'
  have hc' : k * n = n * k := congrArg Subtype.val hc.eq
  rw [Subgroup.mem_bot, commutatorElement_def, hc']
  group

theorem s16e_two_direct_of_sup (F : Cfg2Setting X H J₀ J₁) (hE₀ : Z391.EndUnitsTrivial H J₀)
    (hE₁ : Z391.EndUnitsTrivial H J₁)
    (hsup : s16e_two_cent X H ⊔ s16e_two_fixIrr X H = X) :
    IsInternalDirect (s16e_two_cent X H) (s16e_two_fixIrr X H) X :=
  ⟨s16e_two_commutator_cent_fixIrr F hE₀ hE₁, s16e_two_cent_inf_fixIrr F hE₀ hE₁, hsup⟩

theorem s16e_two_card_dvd_six_mul_aut (F : Cfg2Setting X H J₀ J₁)
    (hE₀ : Z391.EndUnitsTrivial H J₀) (hE₁ : Z391.EndUnitsTrivial H J₁) :
    Nat.card ↥X ∣ 6 * Nat.card (MulAut ↥H) :=
  (s16e_two_card_dvd_mul_aut F).trans
    (Nat.mul_dvd_mul_right (s16e_two_card_cent_dvd_six F hE₀ hE₁) _)

theorem s16e_two_transitive_of_three_dvd (F : Cfg2Setting X H J₀ J₁)
    (hE₀ : Z391.EndUnitsTrivial H J₀) (hE₁ : Z391.EndUnitsTrivial H J₁)
    (h3 : 3 ∣ Nat.card ↥(s16e_two_cent X H)) :
    ∀ I₁ ∈ irrSet H, ∀ I₂ ∈ irrSet H, ∃ k ∈ s16e_two_cent X H, I₂ = I₁.map k.toMonoidHom := by
  intro I₁ hI₁ I₂ hI₂
  haveI : Finite (Subgroup W) := Finite.of_injective _ SetLike.coe_injective
  have hf := s16e_two_irrAct_cent_injective F hE₀ hE₁
  have hle := s16e_two_irrSet_card_le_three F hE₀
  obtain ⟨-, htr⟩ := s16e_twoB_dvd_perm ((s16e_two_irrAct F).comp
    (Subgroup.inclusion (inf_le_left : s16e_two_cent X H ≤ X))) hf hle h3
  obtain ⟨k, hk⟩ := htr ⟨I₁, hI₁⟩ ⟨I₂, hI₂⟩
  refine ⟨k, k.2, ?_⟩
  have := congrArg Subtype.val hk
  simpa [s16e_two_irrAct_apply] using this.symm

private theorem s16e_twoB_cfg2_cent (F : Cfg2Setting X H J₀ J₁) :
    Cfg2Setting (Subgroup.centralizer (H : Set (MulAut W))) H J₀ J₁ := by
  refine ⟨F.sq, ?_, F.simple, F.perfect, F.fix, F.irr₀, F.irr₁, F.inf_eq, F.sup_eq⟩
  intro x hx
  ext y
  constructor
  · rintro ⟨h, hh, rfl⟩
    have h1 : h * x = x * h := Subgroup.mem_centralizer_iff.1 hx h hh
    have h2 : (MulAut.conj x).toMonoidHom h = h := by
      show x * h * x⁻¹ = h
      rw [mul_inv_eq_iff_eq_mul]
      exact h1.symm
    rw [h2]
    exact hh
  · intro hy
    refine ⟨y, hy, ?_⟩
    have h1 : y * x = x * y := Subgroup.mem_centralizer_iff.1 hx y hy
    show x * y * x⁻¹ = y
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.symm

private theorem s16e_twoB_shear (F : Cfg2Setting X H J₀ J₁) {k : MulAut W}
    (hkc : k ∈ Subgroup.centralizer (H : Set (MulAut W)))
    (hk : J₀.map k.toMonoidHom = J₁) :
    ∃ γ : MulAut W, γ ∈ Subgroup.centralizer (H : Set (MulAut W)) ∧
      ∀ a ∈ J₀, γ a = a * k a := by
  have hJ₀ : StableUnder H J₀ := (s16e_two_isIrrOn_of_mem F F.irr₀).2.1
  have hJ₁ : StableUnder H J₁ := (s16e_two_isIrrOn_of_mem F F.irr₁).2.1
  have hinj : Function.Injective (J₀.subtype.coprod J₁.subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have hab' : (a : W) * (b : W) = 1 := by simpa using hab
    have h1 : (a : W) = (b : W)⁻¹ := eq_inv_of_mul_eq_one_left hab'
    have h2 : (a : W) ∈ J₀ ⊓ J₁ := ⟨a.2, by rw [h1]; exact J₁.inv_mem b.2⟩
    rw [F.inf_eq, Subgroup.mem_bot] at h2
    have h3 : (b : W) = 1 := by rw [h2, one_mul] at hab'; exact hab'
    exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)
  have hsurj : Function.Surjective (J₀.subtype.coprod J₁.subtype) := by
    intro w
    have hw : w ∈ J₀ ⊔ J₁ := by rw [F.sup_eq]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hw
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), by simp⟩
  let ε : ↥J₀ × ↥J₁ ≃* W := MulEquiv.ofBijective (J₀.subtype.coprod J₁.subtype) ⟨hinj, hsurj⟩
  have hε : ∀ (a : ↥J₀) (b : ↥J₁), ε (a, b) = (a : W) * (b : W) := fun a b => by
    show (J₀.subtype.coprod J₁.subtype) (a, b) = _
    simp [MonoidHom.coprod_apply]
  let pr : W →* W := J₀.subtype.comp ((MonoidHom.fst ↥J₀ ↥J₁).comp ε.symm.toMonoidHom)
  have hpr₀ : ∀ a ∈ J₀, pr a = a := by
    intro a ha
    have : ε.symm a = (⟨a, ha⟩, 1) := by
      rw [MulEquiv.symm_apply_eq, hε]
      simp
    simp [pr, this]
  have hpr₁ : ∀ b ∈ J₁, pr b = 1 := by
    intro b hb
    have : ε.symm b = (1, ⟨b, hb⟩) := by
      rw [MulEquiv.symm_apply_eq, hε]
      simp
    simp [pr, this]
  have hprJ : ∀ w, pr w ∈ J₀ := fun w => (ε.symm w).1.2
  have hkJ : ∀ a ∈ J₀, k a ∈ J₁ := fun a ha =>
    hk ▸ Subgroup.mem_map_of_mem k.toMonoidHom ha
  let φ : W →* W := MonoidHom.id W * (k.toMonoidHom.comp pr)
  have hφ : ∀ w, φ w = w * k (pr w) := fun w => rfl
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    rw [hφ] at hw
    have h1 : w = (k (pr w))⁻¹ := eq_inv_of_mul_eq_one_left hw
    have h2 : w ∈ J₁ := by rw [h1]; exact J₁.inv_mem (hkJ _ (hprJ w))
    have h3 : pr w = 1 := hpr₁ w h2
    rw [h3, map_one, mul_one] at hw
    exact hw
  have hφbij : Function.Bijective φ := Finite.injective_iff_bijective.1 hφinj
  let γ : MulAut W := MulEquiv.ofBijective φ hφbij
  have hγ : ∀ w, γ w = w * k (pr w) := fun w => rfl
  refine ⟨γ, ?_, fun a ha => by rw [hγ, hpr₀ a ha]⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hcomm : ∀ x, h (k x) = k (h x) := fun x => by
    have := Subgroup.mem_centralizer_iff.1 hkc h hh
    exact congrArg (fun f : MulAut W => f x) this
  ext w
  have hw : w ∈ J₀ ⊔ J₁ := by rw [F.sup_eq]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hw
  have hpa : pr (a * b) = a := by rw [map_mul, hpr₀ a ha, hpr₁ b hb, mul_one]
  have hpa' : pr (h (a * b)) = h a := by
    rw [map_mul, map_mul, hpr₀ _ (hJ₀ h hh a ha), hpr₁ _ (hJ₁ h hh b hb), mul_one]
  show h (γ (a * b)) = γ (h (a * b))
  rw [hγ (a * b), hγ (h (a * b)), hpa, hpa', map_mul h, map_mul h, hcomm]

private theorem s16e_twoB_mul_comm_of_commutator (F : Cfg2Setting X H J₀ J₁)
    (hcomm : ⁅s16e_two_cent X H, s16e_two_fixIrr X H⁆ = ⊥) :
    ∀ k ∈ s16e_two_cent X H, ∀ n ∈ s16e_two_fixIrr X H, k * n = n * k := by
  intro k hk n hn
  have h := Subgroup.commutator_mem_commutator hk hn
  rw [hcomm, Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.1 h

private theorem s16e_twoB_map_mul (x y : MulAut W) (I : Subgroup W) :
    I.map (x * y).toMonoidHom = (I.map y.toMonoidHom).map x.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem s16e_twoB_decomp (F : Cfg2Setting X H J₀ J₁)
    (hcomm : ⁅s16e_two_cent X H, s16e_two_fixIrr X H⁆ = ⊥)
    (hsup : s16e_two_cent X H ⊔ s16e_two_fixIrr X H = X) {g : MulAut W} (hg : g ∈ X) :
    ∃ k ∈ s16e_two_cent X H, ∃ n ∈ s16e_two_fixIrr X H, g = k * n :=
  s16e_two_mem_sup_of_commute (s16e_twoB_mul_comm_of_commutator F hcomm) (hsup.ge hg)

private theorem s16e_twoB_exists_cent_map (F : Cfg2Setting X H J₀ J₁)
    (hcomm : ⁅s16e_two_cent X H, s16e_two_fixIrr X H⁆ = ⊥)
    (hsup : s16e_two_cent X H ⊔ s16e_two_fixIrr X H = X) {g : MulAut W} (hg : g ∈ X)
    {I : Subgroup W} (hI : I ∈ irrSet H) :
    ∃ k ∈ s16e_two_cent X H, I.map g.toMonoidHom = I.map k.toMonoidHom := by
  obtain ⟨k, hk, n, hn, rfl⟩ := s16e_twoB_decomp F hcomm hsup hg
  exact ⟨k, hk, by rw [s16e_twoB_map_mul, hn.2 I hI]⟩

private theorem s16e_twoB_three_dvd_of_trans (F : Cfg2Setting X H J₀ J₁)
    (hE₀ : Z391.EndUnitsTrivial H J₀) (hE₁ : Z391.EndUnitsTrivial H J₁)
    (hcomm : ⁅s16e_two_cent X H, s16e_two_fixIrr X H⁆ = ⊥)
    (hsup : s16e_two_cent X H ⊔ s16e_two_fixIrr X H = X)
    (hT : ∀ I₁ ∈ irrSet H, ∀ I₂ ∈ irrSet H, ∃ g ∈ X, I₂ = I₁.map g.toMonoidHom) :
    3 ∣ Nat.card ↥(s16e_two_cent X H) := by
  haveI : Finite (Subgroup W) := Finite.of_injective _ SetLike.coe_injective
  have hKT : ∀ I₁ ∈ irrSet H, ∀ I₂ ∈ irrSet H,
      ∃ k ∈ s16e_two_cent X H, I₂ = I₁.map k.toMonoidHom := by
    intro I₁ hI₁ I₂ hI₂
    obtain ⟨g, hg, hgI⟩ := hT I₁ hI₁ I₂ hI₂
    obtain ⟨k, hk, hkI⟩ := s16e_twoB_exists_cent_map F hcomm hsup hg hI₁
    exact ⟨k, hk, hgI.trans hkI⟩
  obtain ⟨k, hk, hk01⟩ := hKT J₀ F.irr₀ J₁ F.irr₁
  have hkc : k ∈ Subgroup.centralizer (H : Set (MulAut W)) := (Subgroup.mem_inf.1 hk).2
  obtain ⟨γ, hγc, hγ⟩ := s16e_twoB_shear F hkc hk01.symm
  have hI' : J₀.map γ.toMonoidHom ∈ irrSet H :=
    s16e_two_map_mem_irrSet (s16e_twoB_cfg2_cent F) hγc F.irr₀
  have hJ₀bot : (⊥ : Subgroup W) < J₀ := (s16e_two_isIrrOn_of_mem F F.irr₀).1
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hJ₀bot.ne'
  have ha1' : (a : W) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hbot_of_mem : ∀ y : W, y ∈ J₀ → y ∈ J₁ → y = 1 := fun y h0 h1 => by
    have : y ∈ J₀ ⊓ J₁ := ⟨h0, h1⟩
    rw [F.inf_eq, Subgroup.mem_bot] at this
    exact this
  have kaJ₁ : k (a : W) ∈ J₁ := by
    rw [hk01]
    exact Subgroup.mem_map_of_mem k.toMonoidHom a.2
  have γaI' : γ (a : W) ∈ J₀.map γ.toMonoidHom :=
    Subgroup.mem_map_of_mem γ.toMonoidHom a.2
  have hγa : γ (a : W) = a * k a := hγ a a.2
  have hI'J₀ : J₀.map γ.toMonoidHom ≠ J₀ := by
    intro h
    have h1 : γ (a : W) ∈ J₀ := h.le γaI'
    rw [hγa] at h1
    have h2 : k (a : W) ∈ J₀ := by
      have := J₀.mul_mem (J₀.inv_mem a.2) h1
      rwa [inv_mul_cancel_left] at this
    exact ha1' (k.injective (by rw [hbot_of_mem _ h2 kaJ₁, map_one]))
  have hI'J₁ : J₀.map γ.toMonoidHom ≠ J₁ := by
    intro h
    have h1 : γ (a : W) ∈ J₁ := h.le γaI'
    rw [hγa] at h1
    have h2 : (a : W) ∈ J₁ := by
      have := J₁.mul_mem h1 (J₁.inv_mem kaJ₁)
      rwa [mul_inv_cancel_right] at this
    exact ha1' (hbot_of_mem _ a.2 h2)
  have hJ₀J₁ : J₀ ≠ J₁ := by
    intro h
    exact ha1' (hbot_of_mem _ a.2 (h.le a.2))
  let f : ↥(s16e_two_cent X H) →* Equiv.Perm ↥(irrSet H) := (s16e_two_irrAct F).comp
    (Subgroup.inclusion (inf_le_left : s16e_two_cent X H ≤ X))
  have hfapply : ∀ (κ : ↥(s16e_two_cent X H)) (I : ↥(irrSet H)),
      (f κ I : Subgroup W) = (I : Subgroup W).map (κ : MulAut W).toMonoidHom := fun κ I => rfl
  let S : Set ↥(irrSet H) := Set.range fun κ : ↥(s16e_two_cent X H) => f κ ⟨J₀, F.irr₀⟩
  have h0 : (⟨J₀, F.irr₀⟩ : ↥(irrSet H)) ∈ S :=
    ⟨1, by show f 1 ⟨J₀, F.irr₀⟩ = ⟨J₀, F.irr₀⟩; rw [map_one]; rfl⟩
  have h1 : (⟨J₁, F.irr₁⟩ : ↥(irrSet H)) ∈ S :=
    ⟨⟨k, hk⟩, Subtype.ext ((hfapply _ _).trans hk01.symm)⟩
  have h2 : (⟨J₀.map γ.toMonoidHom, hI'⟩ : ↥(irrSet H)) ∈ S := by
    obtain ⟨k', hk', hk'I⟩ := hKT J₀ F.irr₀ _ hI'
    exact ⟨⟨k', hk'⟩, Subtype.ext ((hfapply _ _).trans hk'I.symm)⟩
  have h3le : 3 ≤ S.ncard :=
    s16e_twoB_three_le_ncard h0 h1 h2 (fun h => hJ₀J₁ (congrArg Subtype.val h))
      (fun h => hI'J₀ (congrArg Subtype.val h).symm)
      (fun h => hI'J₁ (congrArg Subtype.val h).symm)
  have hSle : S.ncard ≤ 3 :=
    calc S.ncard ≤ (Set.univ : Set ↥(irrSet H)).ncard := Set.ncard_le_ncard (Set.subset_univ S)
      _ = Nat.card ↥(irrSet H) := Set.ncard_univ _
      _ ≤ 3 := s16e_two_irrSet_card_le_three F hE₀
  have hdvd : S.ncard ∣ Nat.card ↥(s16e_two_cent X H) :=
    s16e_twoB_orbit_dvd f ⟨J₀, F.irr₀⟩
  have hS3 : S.ncard = 3 := le_antisymm hSle h3le
  rw [hS3] at hdvd
  exact hdvd

theorem s16e_two_three_dvd_of_trans (F : Cfg2Setting X H J₀ J₁) (hE₀ : Z391.EndUnitsTrivial H J₀)
    (hE₁ : Z391.EndUnitsTrivial H J₁) (hsup : s16e_two_cent X H ⊔ s16e_two_fixIrr X H = X)
    (hT : ∀ I₁ ∈ irrSet H, ∀ I₂ ∈ irrSet H, ∃ g ∈ X, I₂ = I₁.map g.toMonoidHom) :
    3 ∣ Nat.card ↥(s16e_two_cent X H) :=
  s16e_twoB_three_dvd_of_trans F hE₀ hE₁
    (s16e_two_commutator_cent_fixIrr F hE₀ hE₁) hsup hT

private theorem s16e_twoB_card_cent_eq_six (F : Cfg2Setting X H J₀ J₁)
    (hE₀ : Z391.EndUnitsTrivial H J₀)
    (hE₁ : Z391.EndUnitsTrivial H J₁)
    (hcomm : ⁅s16e_two_cent X H, s16e_two_fixIrr X H⁆ = ⊥)
    (hsup : s16e_two_cent X H ⊔ s16e_two_fixIrr X H = X)
    (h3 : 3 ∣ Nat.card ↥(s16e_two_cent X H))
    (hno3 : ∀ Nn : Subgroup ↥X, Nn.Normal → Nn.index ≠ 3) :
    Nat.card ↥(s16e_two_cent X H) = 6 := by
  haveI : Finite (Subgroup W) := Finite.of_injective _ SetLike.coe_injective
  have hdvd := s16e_two_card_cent_dvd_six F hE₀ hE₁
  have hle6 : Nat.card ↥(s16e_two_cent X H) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨c, hc⟩ := h3
  have hpos : 0 < Nat.card ↥(s16e_two_cent X H) := Nat.card_pos
  have hcases : Nat.card ↥(s16e_two_cent X H) = 3 ∨ Nat.card ↥(s16e_two_cent X H) = 6 := by
    omega
  rcases hcases with h | h
  · exfalso
    have hf : Function.Injective ((s16e_two_irrAct F).comp
        (Subgroup.inclusion (inf_le_left : s16e_two_cent X H ≤ X))) :=
      s16e_two_irrAct_cent_injective F hE₀ hE₁
    have hrange : (s16e_two_irrAct F).range = ((s16e_two_irrAct F).comp
        (Subgroup.inclusion (inf_le_left : s16e_two_cent X H ≤ X))).range := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        obtain ⟨k, hk, n, hn, hx⟩ := s16e_twoB_decomp F hcomm hsup x.2
        have hkX : k ∈ X := (Subgroup.mem_inf.1 hk).1
        have hxk : s16e_two_irrAct F x = s16e_two_irrAct F ⟨k, hkX⟩ := by
          apply Equiv.ext
          intro I
          apply Subtype.ext
          rw [s16e_two_irrAct_apply, s16e_two_irrAct_apply]
          have hx' : (x : MulAut W) = k * n := hx
          show (I : Subgroup W).map (x : MulAut W).toMonoidHom =
            (I : Subgroup W).map k.toMonoidHom
          rw [hx', s16e_twoB_map_mul, hn.2 I.1 I.2]
        exact ⟨⟨k, hk⟩, hxk.symm⟩
      · rintro _ ⟨k, rfl⟩
        exact ⟨_, rfl⟩
    have hidx : ((s16e_two_irrAct F).ker).index = 3 := by
      rw [Subgroup.index_ker, hrange]
      have := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
      rw [← this]
      exact h
    exact hno3 _ (MonoidHom.normal_ker _) hidx
  · exact h

theorem s16e_two_card_cent_eq_six (F : Cfg2Setting X H J₀ J₁) (hE₀ : Z391.EndUnitsTrivial H J₀)
    (hE₁ : Z391.EndUnitsTrivial H J₁) (hsup : s16e_two_cent X H ⊔ s16e_two_fixIrr X H = X)
    (h3 : 3 ∣ Nat.card ↥(s16e_two_cent X H))
    (hno3 : ∀ Nn : Subgroup ↥X, Nn.Normal → Nn.index ≠ 3) :
    Nat.card ↥(s16e_two_cent X H) = 6 :=
  s16e_twoB_card_cent_eq_six F hE₀ hE₁ (s16e_two_commutator_cent_fixIrr F hE₀ hE₁) hsup h3 hno3

theorem s16e_two_isSym_of_sup (F : Cfg2Setting X H J₀ J₁) (hE₀ : Z391.EndUnitsTrivial H J₀)
    (hE₁ : Z391.EndUnitsTrivial H J₁) (hsup : s16e_two_cent X H ⊔ s16e_two_fixIrr X H = X)
    (h3 : 3 ∣ Nat.card ↥(s16e_two_cent X H))
    (hno3 : ∀ Nn : Subgroup ↥X, Nn.Normal → Nn.index ≠ 3) :
    IsSym ↥(s16e_two_cent X H) 3 :=
  s16e_two_isSym_of_card_six F hE₀ hE₁ (s16e_two_card_cent_eq_six F hE₀ hE₁ hsup h3 hno3)

theorem s16e_two_isSym_direct_of_trans (F : Cfg2Setting X H J₀ J₁)
    (hE₀ : Z391.EndUnitsTrivial H J₀) (hE₁ : Z391.EndUnitsTrivial H J₁)
    (hsup : s16e_two_cent X H ⊔ s16e_two_fixIrr X H = X)
    (hT : ∀ I₁ ∈ irrSet H, ∀ I₂ ∈ irrSet H, ∃ g ∈ X, I₂ = I₁.map g.toMonoidHom)
    (hno3 : ∀ Nn : Subgroup ↥X, Nn.Normal → Nn.index ≠ 3) :
    IsSym ↥(s16e_two_cent X H) 3 ∧
      IsInternalDirect (s16e_two_cent X H) (s16e_two_fixIrr X H) X :=
  ⟨s16e_two_isSym_of_sup F hE₀ hE₁ hsup (s16e_two_three_dvd_of_trans F hE₀ hE₁ hsup hT) hno3,
    s16e_two_direct_of_sup F hE₀ hE₁ hsup⟩

end Structure

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
