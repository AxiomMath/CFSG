module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95COne

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank Module
open scoped commutatorElement

namespace KS93

section Siegel

variable {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {Γ : Type*} [Group Γ]

private theorem exists_eq_add_of_finrank_le_two {W : Submodule K E} (hW : finrank K W ≤ 2)
    {p d : E} (hp : p ∈ W) (hd : d ∈ W) (hd0 : d ≠ 0) (hpd : ∀ c : K, p ≠ c • d) {e : E}
    (he : e ∈ W) : ∃ a b : K, e = a • p + b • d := by
  have hli : LinearIndependent K ![d, p] :=
    (LinearIndependent.pair_iff' hd0).mpr fun a h => hpd a h.symm
  have hrange : Set.range ![d, p] = {d, p} := Matrix.range_cons_cons_empty d p ![]
  have hspan : Submodule.span K ({d, p} : Set E) ≤ W := by
    rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hd
    · exact hp
  have hdim : finrank K (Submodule.span K ({d, p} : Set E)) = 2 := by
    rw [← hrange, finrank_span_eq_card hli]
    simp
  have heq : Submodule.span K ({d, p} : Set E) = W :=
    Submodule.eq_of_le_of_finrank_le hspan (by omega)
  have he' : e ∈ Submodule.span K ({d, p} : Set E) := by
    rw [heq]
    exact he
  obtain ⟨b, a, hab⟩ := Submodule.mem_span_pair.mp he'
  exact ⟨a, b, by rw [← hab, add_comm]⟩

theorem siegel_fix_eq_add [Finite K] {B : LinearMap.BilinForm K E} {Qf : E → K}
    {α : Γ →* (E ≃ₗ[K] E)} {U : Submodule K E} {b₀ : E} (hQ : HS9.IsQuadSpace B Qf)
    (hS : HS9.Siegel B Qf α U b₀) (m : ℕ)
    (hfaith : ∀ g : Γ, (∀ u ∈ U, α g u = u) → ∀ e, α g e = e)
    (hcard : Nat.card K ^ (m + 1) ≤ α.ker.index) (hdim : finrank K U ≤ m + 2)
    {p : E} (hpU : p ∈ U) (hpd : ∀ c : K, p ≠ c • b₀) {e : E} (heU : e ∈ U)
    (hfix : ∀ g, α g p = p → α g e = e) : ∃ a b : K, e = a • p + b • b₀ := by
  classical
  obtain ⟨a₀, ha₀⟩ := hS.exists_dual hQ
  have hadd : ∀ g g' : Γ,
      B (α (g * g') p - p) a₀ = B (α g p - p) a₀ + B (α g' p - p) a₀ := fun g g' => by
    rw [hS.sub_mul hQ g g' hpU, LinearMap.map_add₂]
  let f : Γ →* Multiplicative K :=
    { toFun := fun g => Multiplicative.ofAdd (B (α g p - p) a₀)
      map_one' := by simp
      map_mul' := fun g g' => by simp only [hadd, ofAdd_add] }
  have hfker : ∀ g, g ∈ f.ker ↔ α g p = p := fun g => by
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (B (α g p - p) a₀) = 1 ↔ _
    rw [ofAdd_eq_one]
    constructor
    · intro h
      have h1 := hS.sub_eq_smul hQ g hpU ha₀
      rw [h, zero_smul] at h1
      exact sub_eq_zero.mp h1
    · intro h
      rw [h, sub_self, LinearMap.map_zero₂]
  have hkerle : α.ker ≤ f.ker := fun g hg => by
    rw [hfker, MonoidHom.mem_ker.mp hg]
    rfl
  have hidx : f.ker.index ≤ Nat.card K := by
    rw [Subgroup.index_ker f]
    haveI : Finite (Multiplicative K) := inferInstanceAs (Finite K)
    calc Nat.card f.range ≤ Nat.card (Multiplicative K) := Subgroup.card_le_card_group _
      _ = Nat.card K := Nat.card_congr Multiplicative.toAdd
  have hcard' : Nat.card K ^ m ≤ α.ker.relIndex f.ker := by
    have hmul := Subgroup.relIndex_mul_index hkerle
    have h1 : Nat.card K ^ m * Nat.card K ≤ α.ker.relIndex f.ker * Nat.card K :=
      calc Nat.card K ^ m * Nat.card K = Nat.card K ^ (m + 1) := (pow_succ _ _).symm
        _ ≤ α.ker.index := hcard
        _ = α.ker.relIndex f.ker * f.ker.index := hmul.symm
        _ ≤ α.ker.relIndex f.ker * Nat.card K := Nat.mul_le_mul_left _ hidx
    exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos
  have h := hS.finrank_fix_le hQ f.ker m (fun g _ hg => hfaith g hg) hcard'
  have hW : finrank K ↥(U ⊓ HS9.fixSpace α f.ker) ≤ 2 := by omega
  exact exists_eq_add_of_finrank_le_two hW
    ⟨hpU, HS9.mem_fixSpace.mpr fun g hg => (hfker g).mp hg⟩
    ⟨hS.mem, HS9.mem_fixSpace.mpr fun g _ => hS.fix g⟩ hS.ne hpd
    ⟨heU, HS9.mem_fixSpace.mpr fun g hg => hfix g ((hfker g).mp hg)⟩

end Siegel

section Phi

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {K' : Type} [Field K']
  {γ : G → K'} {M₀ : Tim79.QuadModel Q Z K' γ}

theorem pi_commutator (hc : Ctx M Q Z B) (φ₀ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K'] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ₀ m (M₀.π x))
    (g : H0 M Z) {x : G} (hx : x ∈ Q) :
    ⁅(g : G), x⁆ ∈ Q ∧ M₀.π ⁅(g : G), x⁆ = φ₀ g (M₀.π x) - M₀.π x := by
  have hgM : (g : G) ∈ M := (Subgroup.mem_inf.mp g.2).1
  have hgx : (g : G) * x * (g : G)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgM) x).mp hx
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact Q.mul_mem hgx (Q.inv_mem hx)
  · rw [commutatorElement_def, M₀.π_mul _ hgx _ (Q.inv_mem hx), M₀.pi_inv hx, hφπ g x hx,
      sub_eq_add_neg]

theorem mem_range_sub_one_iff (hc : Ctx M Q Z B) (φ₀ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K'] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ₀ m (M₀.π x))
    (hφQ : ∀ m : H0 M Z, φ₀ m = 1 ↔ (m : G) ∈ Q) (s : H0 M Z) (hs2 : (s : G) ^ 2 ∈ Q)
    {V : Subgroup G} (hV : ⁅Q, Subgroup.zpowers (s : G)⁆ ⊔ Z = V) (e : M₀.E) :
    e ∈ LinearMap.range ((φ₀ s : M₀.E →ₗ[K'] M₀.E) - 1) ↔ e ∈ M₀.img V := by
  have hΦe : ∀ f, ((φ₀ s : M₀.E →ₗ[K'] M₀.E) - 1) f = φ₀ s f - f := fun f => rfl
  constructor
  · intro he
    obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp he
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj f
    obtain ⟨hcQ, hcπ⟩ := pi_commutator hc φ₀ hφπ s hx
    rw [hΦe, ← hcπ]
    refine M₀.pi_mem_img ?_ hcQ
    rw [← hV]
    refine Subgroup.mem_sup_left ?_
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers _))
  · intro he
    obtain ⟨v, hvV, hvQ, rfl⟩ := M₀.mem_img.mp he
    obtain ⟨H', hH'⟩ : ∃ H' : Subgroup G, ∀ x, x ∈ H' ↔
        x ∈ Q ∧ M₀.π x ∈ LinearMap.range ((φ₀ s : M₀.E →ₗ[K'] M₀.E) - 1) :=
      ⟨{ carrier := {x | x ∈ Q ∧ M₀.π x ∈ LinearMap.range ((φ₀ s : M₀.E →ₗ[K'] M₀.E) - 1)}
         mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, by
           rw [M₀.π_mul _ ha.1 _ hb.1]
           exact add_mem ha.2 hb.2⟩
         one_mem' := ⟨Q.one_mem, by
           rw [M₀.pi_one]
           exact zero_mem _⟩
         inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, by
           rw [M₀.pi_inv ha.1]
           exact neg_mem ha.2⟩ }, fun x => Iff.rfl⟩
    have hT2 : φ₀ s * φ₀ s = 1 := by
      rw [← map_mul, hφQ]
      show (s : G) * (s : G) ∈ Q
      rw [← pow_two]
      exact hs2
    have hVH : V ≤ H' := by
      rw [← hV]
      refine sup_le (Subgroup.commutator_le.mpr fun x hx g hg => ?_) fun x hx => ?_
      · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        have hsk : (s : G) ^ k = ((s ^ k : H0 M Z) : G) := by simp
        rw [hsk, ← commutatorElement_inv]
        refine H'.inv_mem ?_
        obtain ⟨hcQ, hcπ⟩ := pi_commutator hc φ₀ hφπ (s ^ k) hx
        refine (hH' _).mpr ⟨hcQ, ?_⟩
        rw [hcπ, map_zpow]
        obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
        · rw [hj, zpow_mul, zpow_two, hT2, one_zpow,
            show (1 : M₀.E ≃ₗ[K'] M₀.E) (M₀.π x) = M₀.π x from rfl, sub_self]
          exact zero_mem _
        · rw [hj, zpow_add_one, zpow_mul, zpow_two, hT2, one_zpow, one_mul]
          exact LinearMap.mem_range.mpr ⟨M₀.π x, hΦe _⟩
      · have hxQ : x ∈ Q := hc.hyp.Z_normal.1 hx
        refine (hH' x).mpr ⟨hxQ, ?_⟩
        rw [(M₀.π_ker x hxQ).mpr hx]
        exact zero_mem _
    exact ((hH' v).mp (hVH hvV)).2

omit [Finite G] in
theorem phi_mul_comm {φ₀ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K'] M₀.E)}
    (hφQ : ∀ m : H0 M Z, φ₀ m = 1 ↔ (m : G) ∈ Q) (a b : H0 M Z) (hab : ⁅(a : G), (b : G)⁆ ∈ Q) :
    φ₀ a * φ₀ b = φ₀ b * φ₀ a := by
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, hφQ]
  exact hab

end Phi

section Stab

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}

theorem fix_stab_eq_add {X : Subgroup G} (hcX : Ctx M Q Z X) {n : ℕ} (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q X)) (hLX : Nat.card (LB M Q X) = Nat.card Q * Nat.card Z ^ (n - 1))
    {K' : Type} [Field K'] [Finite K'] {γ : G → K'} {M₀ : Tim79.QuadModel Q Z K' γ}
    (h : GlobalModelData M Q Z γ M₀) (φ₀ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K'] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ₀ m (M₀.π x))
    (hφQ : ∀ m : H0 M Z, φ₀ m = 1 ↔ (m : G) ∈ Q)
    (hφiso : ∀ (m : H0 M Z) e, M₀.Qf (φ₀ m e) = M₀.Qf e)
    {U : Submodule K' M₀.E} (hUmem : ∀ e, e ∈ U ↔ e ∈ M₀.img (Q ⊓ QB X))
    (hUdim : finrank K' U = n) (hUsing : ∀ e ∈ U, M₀.Qf e = 0)
    (hUperp : ∀ e, (∀ u ∈ U, M₀.B u e = 0) → e ∈ U)
    {d : M₀.E} (hd0 : d ≠ 0) (hds : M₀.Qf d = 0)
    (hdX : ∀ v, v ∈ M₀.img X ↔ ∃ c : K', v = c • d)
    (hdcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (X : Set G) ↔ M₀.B (M₀.π x) d = 0)
    {p : M₀.E} (hpU : p ∈ U) (hpd : ∀ c : K', p ≠ c • d) {e : M₀.E} (heU : e ∈ U)
    (hfix : ∀ (l : G) (hl : l ∈ H0 M Z), l ∈ LB M Q X → φ₀ ⟨l, hl⟩ p = p →
      φ₀ ⟨l, hl⟩ e = e) :
    ∃ a b : K', e = a • p + b • d := by
  classical
  have hQ : HS9.IsQuadSpace M₀.B M₀.Qf := ⟨M₀.alt, M₀.nondeg, M₀.Qf_add⟩
  have hdU : d ∈ U := (hUmem d).mpr (M₀.img_mono (le_inf hcX.le hcX.B_le_QB)
    ((hdX d).mpr ⟨1, (one_smul K' d).symm⟩))
  let α : ↥(LB M Q X) →* (M₀.E ≃ₗ[K'] M₀.E) := φ₀.comp (Subgroup.inclusion hcX.LB_le_H0)
  have hαπ : ∀ (l : ↥(LB M Q X)) (x : G), x ∈ Q →
      M₀.π ((l : G) * x * (l : G)⁻¹) = α l (M₀.π x) := fun l x hx =>
    hφπ ⟨(l : G), hcX.LB_le_H0 l.2⟩ x hx
  have hα1 : ∀ l : ↥(LB M Q X), α l = 1 ↔ (l : G) ∈ Q := fun l =>
    hφQ ⟨(l : G), hcX.LB_le_H0 l.2⟩
  have hαiso : ∀ (l : ↥(LB M Q X)) e, M₀.Qf (α l e) = M₀.Qf e := fun l e =>
    hφiso ⟨(l : G), hcX.LB_le_H0 l.2⟩ e
  have hS : HS9.Siegel M₀.B M₀.Qf α U d := by
    refine ⟨hαiso, fun l e => ?_, hUsing, hUperp, hdU, hd0, fun l => ?_, fun l u hu => ?_⟩
    · have h1 : α l * α l = 1 := by
        rw [← map_mul, hα1]
        show (l : G) * (l : G) ∈ Q
        rw [← pow_two]
        exact hcX.sq_mem_Q_of_mem_LB l.2
      have := congrArg (fun f : M₀.E ≃ₗ[K'] M₀.E => f e) h1
      simpa using this
    · exact (hcX.LB_act_fix_line h hdX l.2 (T := (α l : M₀.E →ₗ[K'] M₀.E)) (hαπ l)).1
    · obtain ⟨c, hc'⟩ := (hcX.LB_act_fix_line h hdX l.2 (T := (α l : M₀.E →ₗ[K'] M₀.E))
        (hαπ l)).2 u ((hUmem u).mp hu)
      refine ⟨c, ?_⟩
      have : α l u - u = c • d := hc'
      rw [← this]
      abel
  have hfaith : ∀ x : ↥(LB M Q X), (∀ u ∈ U, α x u = u) → ∀ e, α x e = e := by
    intro x hxU e
    obtain ⟨s', hs', y, hy, hxsy⟩ := hcX.exists_mul_of_mem_LB x.2
    have hs'' : s' ∈ QB X ⊓ Subgroup.centralizer (Z : Set G) := by
      rw [← hcX.QB_inf_M_eq]
      exact hs'
    have hsH : s' ∈ H0 M Z := ⟨hs'.2, hs''.2⟩
    have hyH : y ∈ H0 M Z := hcX.LB_le_H0 (sec39_Q_le_LB hy)
    have hxH : (x : G) ∈ H0 M Z := hcX.LB_le_H0 x.2
    have hφx : φ₀ ⟨(x : G), hxH⟩ = φ₀ ⟨s', hsH⟩ := by
      have : (⟨(x : G), hxH⟩ : H0 M Z) = ⟨s', hsH⟩ * ⟨y, hyH⟩ := Subtype.ext hxsy
      rw [this, map_mul, (hφQ ⟨y, hyH⟩).mpr hy, mul_one]
    have hTU : ∀ u ∈ U, φ₀ ⟨s', hsH⟩ u = u := by
      intro u hu
      rw [← hφx]
      exact hxU u hu
    have hsQ : s' ∈ Q := HS9.faithful95 hcX h φ₀ hφπ hφQ hφiso hno hUmem hUsing hUperp hd0 hds
      hdX hdcent hs' hsH hTU
    have hxQ : (x : G) ∈ Q := by
      rw [hxsy]
      exact Q.mul_mem hsQ hy
    rw [(hα1 x).mpr hxQ]
    rfl
  have hker : α.ker = Q.subgroupOf (LB M Q X) := by
    ext x
    rw [MonoidHom.mem_ker, hα1, Subgroup.mem_subgroupOf]
  have hQL : Q ≤ LB M Q X := sec39_Q_le_LB
  have hrel : Q.relIndex (LB M Q X) = Nat.card Z ^ (n - 1) := by
    have h1 : Nat.card (Q.subgroupOf (LB M Q X)) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv
    have h2 := Subgroup.card_mul_index (Q.subgroupOf (LB M Q X))
    rw [h1] at h2
    have h3 : Nat.card Q * Q.relIndex (LB M Q X) = Nat.card Q * Nat.card Z ^ (n - 1) := by
      rw [← hLX]
      exact h2
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h3
  have hn1 : n - 2 + 1 = n - 1 := by omega
  have hcard : Nat.card K' ^ (n - 2 + 1) ≤ α.ker.index := by
    have e1 : α.ker.index = Nat.card K' ^ (n - 2 + 1) := by
      rw [hker, hn1, h.card]
      exact hrel
    exact e1.ge
  exact siegel_fix_eq_add hQ hS (n - 2) hfaith hcard (by omega) hpU hpd heU
    fun l hl => hfix (l : G) (hcX.LB_le_H0 l.2) l.2 hl

end Stab

end KS93

end CFSG.RankThree.GF2n.Stroth80
