module

public import CFSG.Quasithin.Background.A1cA132Prelim

public section

namespace CFSG.Quasithin

open Matrix
open scoped MatrixGroups

namespace A1c

section CoreHom

variable {r p : ℕ} [Fact r.Prime] [hp : Fact p.Prime]

theorem card_le_of_isCyclic_exponent {K : Type*} [Group K] [Finite K] [IsCyclic K]
    (hK : ∀ k : K, k ^ p = 1) : Nat.card K ≤ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K)
  have h1 : orderOf g = Nat.card K := orderOf_eq_card_of_forall_mem_zpowers hg
  have h2 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (hK g)
  rw [← h1]
  exact Nat.le_of_dvd hp.out.pos h2

variable {Q : Type*} [Group Q]

theorem index_det_ker_le (hQexp : ∀ x : Q, x ^ p = 1) (f : Q →* GL (Fin 2) (ZMod r)) :
    (Matrix.GeneralLinearGroup.det.comp f).ker.index ≤ p := by
  rw [Subgroup.index_ker]
  apply card_le_of_isCyclic_exponent
  rintro ⟨_, ⟨q, rfl⟩⟩
  apply Subtype.ext
  simp [← map_pow, hQexp q]

theorem index_ker_subgroupOf_le (hr2 : r ≠ 2) (hp2 : p ≠ 2) (hpr : p ≠ r)
    (hQexp : ∀ x : Q, x ^ p = 1) (f : Q →* GL (Fin 2) (ZMod r)) :
    (f.ker.subgroupOf (Matrix.GeneralLinearGroup.det.comp f).ker).index ≤ p := by
  set D := (Matrix.GeneralLinearGroup.det.comp f).ker with hD
  let fSL : ↥D →* SL(2, ZMod r) :=
    { toFun := fun d => ⟨((f d : GL (Fin 2) (ZMod r)) : Matrix (Fin 2) (Fin 2) (ZMod r)), by
        have h : (d : Q) ∈ (Matrix.GeneralLinearGroup.det.comp f).ker := d.2
        have h2 := congrArg (fun u : (ZMod r)ˣ => (u : ZMod r)) (MonoidHom.mem_ker.1 h)
        simpa using h2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp; rfl) }
  have hker : f.ker.subgroupOf D = fSL.ker := by
    ext d
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      apply Subtype.ext
      show ((f d : GL (Fin 2) (ZMod r)) : Matrix (Fin 2) (Fin 2) (ZMod r)) = 1
      rw [h]
      rfl
    · intro h
      exact Units.ext (congrArg Subtype.val h)
  rw [hker, Subgroup.index_ker]
  refine card_le_of_exponent_sl2 hr2 hp2 hpr fSL.range ?_
  rintro _ ⟨d, rfl⟩
  rw [← map_pow]
  have : (d : Q) ^ p = 1 := hQexp d
  have h3 : d ^ p = 1 := Subtype.ext (by simpa using this)
  rw [h3, map_one]

end CoreHom

section Irred

variable {G : Type*} [Group G]

@[expose] def IsNInv (P : Subgroup G) (U : Subgroup ↥P) : Prop :=
  ∀ n : ↥(Subgroup.normalizer (P : Set G)), U.map (conjAut (N := P) (le_refl _) n).toMonoidHom ≤ U

theorem IsNInv.sup {P : Subgroup G} {U V : Subgroup ↥P} (hU : IsNInv P U) (hV : IsNInv P V) :
    IsNInv P (U ⊔ V) := by
  intro n
  rw [Subgroup.map_sup]
  exact sup_le_sup (hU n) (hV n)

theorem isNInv_subgroupOf {P M : Subgroup G} (hM : M.Normal) : IsNInv P (M.subgroupOf P) := by
  intro n
  rintro _ ⟨u, hu, rfl⟩
  have hu' : (u : G) ∈ M := hu
  have : ((conjAut (N := P) (le_refl _) n u : ↥P) : G) = (n : G) * u * (n : G)⁻¹ := rfl
  show ((conjAut (N := P) (le_refl _) n u : ↥P) : G) ∈ M
  rw [this]
  exact hM.conj_mem _ hu' n

theorem isNInv_frattini (P : Subgroup G) : IsNInv P (frattini ↥P) := by
  intro n
  have := (inferInstance : (frattini ↥P).Characteristic)
  rw [Subgroup.characteristic_iff_map_eq.1 this (conjAut (N := P) (le_refl _) n)]

theorem eq_frattini_or_eq_top_of_ambient {P : Subgroup G}
    (hirr : ∀ U : Subgroup G, frattiniIn P ≤ U → U ≤ P →
      Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (U : Set G) →
      U = frattiniIn P ∨ U = P)
    {U₀ : Subgroup ↥P} (hΦ : frattini ↥P ≤ U₀) (hinv : IsNInv P U₀) :
    U₀ = frattini ↥P ∨ U₀ = ⊤ := by
  have hinj : Function.Injective (Subgroup.map P.subtype : Subgroup ↥P → Subgroup G) :=
    Subgroup.map_injective P.subtype_injective
  have hN : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (U₀.map P.subtype : Set G) := by
    have key : ∀ g : G, g ∈ Subgroup.normalizer (P : Set G) → ∀ x ∈ U₀.map P.subtype,
        g * x * g⁻¹ ∈ U₀.map P.subtype := by
      rintro g hg _ ⟨u, hu, rfl⟩
      exact ⟨conjAut (N := P) (le_refl _) ⟨g, hg⟩ u, hinv ⟨g, hg⟩ ⟨u, hu, rfl⟩, rfl⟩
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
    have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
    simpa [mul_assoc] using this
  rcases hirr (U₀.map P.subtype) (Subgroup.map_mono hΦ) (Subgroup.map_subtype_le U₀) hN with h | h
  · left
    exact hinj h
  · right
    apply hinj
    rw [h, Subgroup.map_top, Subgroup.range_subtype]

end Irred

section GL2

theorem le_one_of_pow_dvd_card_GL2 {p j : ℕ} [hp : Fact p.Prime]
    (h : p ^ j ∣ (p ^ 2 - 1) * (p ^ 2 - p)) : j ≤ 1 := by
  have hp1 : 1 < p := hp.out.one_lt
  have h1 : p ^ 2 - p = p * (p - 1) := by rw [Nat.mul_sub, mul_one, sq]
  have h2 : (p ^ 2 - 1) * (p ^ 2 - p) = p * ((p ^ 2 - 1) * (p - 1)) := by
    rw [h1]; ring
  have hc1 : ¬ p ∣ p ^ 2 - 1 := by
    intro hd
    have : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub (dvd_pow_self p two_ne_zero) hd
    have h3 : p ^ 2 - (p ^ 2 - 1) = 1 := by
      have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    rw [h3] at this
    exact hp.out.one_lt.ne' (Nat.dvd_one.1 this)
  have hc2 : ¬ p ∣ p - 1 := by
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hcop : Nat.Coprime (p ^ j) ((p ^ 2 - 1) * (p - 1)) := by
    apply Nat.Coprime.pow_left
    apply Nat.Coprime.mul_right
    · exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hc1
    · exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hc2
  rw [h2] at h
  have h4 : p ^ j ∣ p := hcop.dvd_of_dvd_mul_right h
  by_contra hj
  push Not at hj
  have h5 : p ^ 2 ∣ p ^ j := pow_dvd_pow p hj
  have h6 := h5.trans h4
  have := Nat.le_of_dvd (by omega) h6
  nlinarith

end GL2

section LemmaK

variable {G : Type*} [Group G] [Finite G] {r p : ℕ} [hr : Fact r.Prime] [hp : Fact p.Prime]

theorem action_trivial_of_irreducible (hr2 : r ≠ 2) (hp2 : p ≠ 2) {P : Subgroup G}
    (hPexp : ∀ x ∈ P, x ^ p = 1) (hΦ : (frattini ↥P).index = p ^ 2)
    (hirr : ∀ U₀ : Subgroup ↥P, frattini ↥P ≤ U₀ → IsNInv P U₀ →
      U₀ = frattini ↥P ∨ U₀ = ⊤)
    {W : Type*} [Group W] [Finite W] (hWc : ∀ a b : W, a * b = b * a) (hWr : ∀ w : W, w ^ r = 1)
    (hWcard : Nat.card W ≤ r ^ 2) (ρ : G →* MulAut W) : P ≤ ρ.ker := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  have hQexp : ∀ x : ↥P, x ^ p = 1 := fun x => Subtype.ext (by simpa using hPexp x x.2)
  let f : ↥P →* MulAut W := ρ.comp P.subtype
  have hfk : f.ker = ρ.ker.subgroupOf P := (MonoidHom.comap_ker ρ P.subtype).symm
  have hCinv : IsNInv P f.ker := by rw [hfk]; exact isNInv_subgroupOf (MonoidHom.normal_ker ρ)
  suffices hC : f.ker = ⊤ by
    intro x hx
    have : (⟨x, hx⟩ : ↥P) ∈ f.ker := by rw [hC]; trivial
    exact this
  rcases hirr (f.ker ⊔ frattini ↥P) le_sup_right (hCinv.sup (isNInv_frattini P)) with h | h
  swap
  · exact frattini_nongenerating h
  exfalso
  have hCΦ : f.ker ≤ frattini ↥P := le_sup_left.trans h.le
  have hdvd : p ^ 2 ∣ f.ker.index := hΦ ▸ Subgroup.index_dvd_of_le hCΦ
  have hidx : p ^ 2 ≤ f.ker.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd
  have hp2' : p < p ^ 2 := by nlinarith
  have hrange_exp : ∀ a ∈ f.range, a ^ p = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow, hQexp x, map_one]
  have hind : f.ker.index = Nat.card f.range := Subgroup.index_ker f
  have hWp : IsPGroup r W := fun w => ⟨1, by simpa using hWr w⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hWp
  have hk2 : k ≤ 2 := by
    have : r ^ k ≤ r ^ 2 := hk ▸ hWcard
    exact (Nat.pow_le_pow_iff_right hr.out.one_lt).1 this
  interval_cases k
  ·
    have hsub : Subsingleton W := by
      have : Nat.card W = 1 := by simpa using hk
      exact (Nat.card_eq_one_iff_unique.1 this).1
    have hf1 : f.ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [MonoidHom.mem_ker]
      ext w
      exact Subsingleton.elim _ _
    rw [hf1, Subgroup.index_top] at hidx
    omega
  ·
    have hn : Nat.card W = r := by simpa using hk
    have hcyc : IsCyclic W := isCyclic_of_prime_card (p := r) hn
    have : Fact (Nat.card W).Prime := ⟨by rw [hn]; exact hr.out⟩
    have hcycAut : IsCyclic (MulAut W) :=
      isCyclic_of_surjective (IsCyclic.mulAutMulEquiv W).symm.toMonoidHom
        (IsCyclic.mulAutMulEquiv W).symm.surjective
    have hrc : IsCyclic ↥f.range := inferInstance
    have h1 : Nat.card f.range ≤ p :=
      card_le_of_isCyclic_exponent (K := ↥f.range) (fun a => Subtype.ext (hrange_exp a a.2))
    omega
  ·
    have hcard : Nat.card W = r ^ 2 := hk
    obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := r)
      hWc hWr hcard
    by_cases hpr : p = r
    ·
      subst hpr
      have hdvd2 : Nat.card f.range ∣ Nat.card (MulAut W) := Subgroup.card_subgroup_dvd_card _
      rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e,
        CFSG.SectionRank.Ccomm.card_GL_zmod, Fin.prod_univ_two] at hdvd2
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at hdvd2
      have hrp : IsPGroup p f.range := fun a => ⟨1, Subtype.ext (by simpa using hrange_exp a a.2)⟩
      obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hrp
      rw [hj] at hdvd2
      have hj1 : j ≤ 1 := le_one_of_pow_dvd_card_GL2 hdvd2
      have : Nat.card f.range ≤ p := by
        rw [hj]
        calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.out.pos hj1
          _ = p := pow_one p
      omega
    ·
      let ε := CFSG.SectionRank.Ccomm.elemAutEquivGL e
      let ρ' : G →* GL (Fin 2) (ZMod r) := ε.toMonoidHom.comp ρ
      let f' : ↥P →* GL (Fin 2) (ZMod r) := ρ'.comp P.subtype
      have hkerf : f'.ker = f.ker := by
        ext x
        rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
        constructor
        · intro hx
          apply ε.injective
          rw [map_one]
          exact hx
        · intro hx
          show ε (f x) = 1
          rw [hx, map_one]
      let θ : G →* (ZMod r)ˣ := Matrix.GeneralLinearGroup.det.comp ρ'
      let D₀ : Subgroup ↥P := (θ.comp P.subtype).ker
      have hD₀ : D₀ = θ.ker.subgroupOf P := (MonoidHom.comap_ker θ P.subtype).symm
      have hD₀' : D₀ = (Matrix.GeneralLinearGroup.det.comp f').ker := rfl
      have hCD : f.ker ≤ D₀ := by
        intro x hx
        rw [← hkerf] at hx
        rw [hD₀', MonoidHom.mem_ker]
        simp [MonoidHom.mem_ker.1 hx]
      have h1 : D₀.index ≤ p := by rw [hD₀']; exact index_det_ker_le hQexp f'
      have h2 : (f'.ker.subgroupOf D₀).index ≤ p := by
        rw [hD₀']
        exact index_ker_subgroupOf_le hr2 hp2 hpr hQexp f'
      have h3 : f.ker.relIndex D₀ = (f'.ker.subgroupOf D₀).index := by
        rw [Subgroup.relIndex, hkerf]
      have h4 : f.ker.relIndex D₀ * D₀.index = f.ker.index := Subgroup.relIndex_mul_index hCD
      have h5 : f.ker.index ≤ p * p := by
        rw [← h4]
        exact Nat.mul_le_mul (h3 ▸ h2) h1
      have h6 : f.ker.index = p ^ 2 := le_antisymm (by simpa [sq] using h5) hidx
      have h7 : f.ker.relIndex D₀ = p ∧ D₀.index = p := by
        have hA : f.ker.relIndex D₀ ≤ p := h3 ▸ h2
        have hpp : p * p = f.ker.relIndex D₀ * D₀.index := by rw [h4, h6, sq]
        have hB : D₀.index = p := by nlinarith
        refine ⟨?_, hB⟩
        rw [hB] at hpp
        exact (Nat.eq_of_mul_eq_mul_right hp.out.pos hpp.symm)
      have h8 : frattini ↥P = f.ker := by
        have h9 : f.ker.relIndex (frattini ↥P) * (frattini ↥P).index = f.ker.index :=
          Subgroup.relIndex_mul_index hCΦ
        rw [hΦ, h6] at h9
        have h10 : f.ker.relIndex (frattini ↥P) = 1 := by
          have : f.ker.relIndex (frattini ↥P) * p ^ 2 = 1 * p ^ 2 := by rw [h9, one_mul]
          exact Nat.eq_of_mul_eq_mul_right (by positivity) this
        exact le_antisymm (Subgroup.relIndex_eq_one.1 h10) hCΦ
      have hD₀inv : IsNInv P D₀ := by
        rw [hD₀]; exact isNInv_subgroupOf (MonoidHom.normal_ker θ)
      rcases hirr D₀ (h8 ▸ hCD) hD₀inv with h' | h'
      · have : f.ker.relIndex D₀ = 1 := by rw [h', h8]; simp
        rw [this] at h7
        exact absurd h7.1 (by omega)
      · rw [h', Subgroup.index_top] at h7
        omega

end LemmaK

end A1c

end CFSG.Quasithin
