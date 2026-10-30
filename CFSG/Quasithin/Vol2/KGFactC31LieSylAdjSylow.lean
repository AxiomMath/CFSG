module

public import CFSG.Quasithin.Vol2.KGFactC31LieSylAdjCheck
public import CFSG.Quasithin.Vol2.KGFactC31LieSylEig
public import CFSG.Quasithin.Vol2.KGFactC31LieSylGen
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcToral
public import CFSG.RankThree.PartOne.KGD.D4Weyl
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.RankThree.PartOne.K133H.F4Weyl

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint

theorem zpowers_isPGroup_of_pow {G : Type*} [Group G] {p : ℕ} {x : G} (hx : x ^ p = 1) :
    IsPGroup p (Subgroup.zpowers x) := by
  intro g
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  have hx' : x ^ (p : ℤ) = 1 := by exact_mod_cast hx
  rw [SubgroupClass.coe_pow, pow_one, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hx',
    one_zpow]
  rfl

theorem sylow_mem_of_comm {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {D : Subgroup G} (hPD : (P : Subgroup G) ≤ D) (hD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    {x : G} (hx : x ∈ D) (hxp : IsPGroup p (Subgroup.zpowers x)) :
    x ∈ (P : Subgroup G) := by
  have hzD : Subgroup.zpowers x ≤ D := Subgroup.zpowers_le.2 hx
  have hC : (P : Subgroup G) ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hD h (hzD hh) g (hPD hg)
  have hN : (P : Subgroup G) ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
    hC.trans (centralizer_le_normalizer_of_set _)
  have hsup : IsPGroup p ((P : Subgroup G) ⊔ Subgroup.zpowers x : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' P.isPGroup' hxp hN
  have hEq := P.is_maximal' hsup le_sup_left
  have hle : Subgroup.zpowers x ≤ (P : Subgroup G) := by
    rw [← hEq]
    exact le_sup_right
  exact hle (Subgroup.mem_zpowers x)

theorem end_eq_one_of_basis {τ : Tag} {K : Type} [Field K]
    (f : Module.End K (RootModule τ K))
    (h : ∀ a : Label τ, f (Finsupp.single a 1) = Finsupp.single a 1) : f = 1 := by
  apply Finsupp.lhom_ext'
  intro a
  apply LinearMap.ext_ring
  simpa using h a

theorem units_eq_one_of_basis {τ : Tag} {K : Type} [Field K]
    (x : (Module.End K (RootModule τ K))ˣ)
    (h : ∀ a : Label τ, (x : Module.End K (RootModule τ K)) (Finsupp.single a 1) =
      Finsupp.single a 1) : x = 1 :=
  Units.ext (end_eq_one_of_basis _ h)

theorem torus_single_eq {τ : Tag}
    {K : Type} [Field K] {g : ModGL τ K} (hg : g ∈ torusGroup τ K) (a : Label τ) :
    (g : Module.End K (RootModule τ K)) (Finsupp.single a 1) =
      ((g : Module.End K (RootModule τ K)) (Finsupp.single a 1) a) • Finsupp.single a 1 := by
  obtain ⟨θ, hfix, hroot⟩ := torus_mem_char hg
  rcases a with i | ⟨β, hβ⟩
  · have h1 : (g : Module.End K (RootModule τ K)) (Finsupp.single (Sum.inl i) 1) =
        Finsupp.single (Sum.inl i) 1 := hfix i
    rw [h1]
    simp
  · have h2 := hroot β hβ
    rw [rootVec_eq_single_of_isRoot hβ] at h2
    rw [h2]
    simp

section Torus


@[expose] noncomputable def iotaM (τ : Tag) (K : Type) [Field K] (ζ : Kˣ) (k : Fin τ.rank → ZMod 11) :
    ModGL τ K :=
  (List.ofFn fun i => torusElt τ K i ζ ^ (k i).val).prod

theorem iotaM_mem {τ : Tag}
    {K : Type} [Field K] (ζ : Kˣ) (k : Fin τ.rank → ZMod 11) :
    iotaM τ K ζ k ∈ torusGroup τ K := by
  unfold iotaM
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact pow_mem (torusElt_mem_torusGroup i ζ) _

theorem iotaM_hVec {τ : Tag} {K : Type} [Field K] (ζ : Kˣ) (k : Fin τ.rank → ZMod 11)
    (l : Fin τ.rank) :
    (iotaM τ K ζ k : Module.End K (RootModule τ K)) (hVec τ K l) = hVec τ K l := by
  have h := units_list_prod_apply _ (fun i => torusElt τ K i ζ ^ (k i).val) (fun _ => (1 : K))
    (hVec τ K l) (fun i => by
      rw [units_pow_apply_of_eigen (torusElt τ K i ζ) (hVec τ K l) 1
        (by rw [torusElt_hVec, one_smul]), one_pow])
  unfold iotaM
  rw [h]
  simp

theorem iotaM_rootVec {τ : Tag} {K : Type} [Field K] (ζ : Kˣ) (k : Fin τ.rank → ZMod 11)
    (β : Fin τ.rank → ℤ) (hβ : IsRoot τ β) :
    (iotaM τ K ζ k : Module.End K (RootModule τ K)) (rootVec τ K β) =
      (∏ i, (((ζ ^ (∑ l, τ.cartan i l * β l) : Kˣ) : K)) ^ (k i).val) • rootVec τ K β := by
  unfold iotaM
  exact units_list_prod_apply _ (fun i => torusElt τ K i ζ ^ (k i).val)
    (fun i => (((ζ ^ (∑ l, τ.cartan i l * β l) : Kˣ) : K)) ^ (k i).val) (rootVec τ K β)
    (fun i => units_pow_apply_of_eigen (torusElt τ K i ζ) (rootVec τ K β) _
      (torusElt_rootVec i ζ hβ) _)

@[expose] def Nexp (τ : Tag) (k : Fin τ.rank → ZMod 11) (β : Fin τ.rank → ℤ) : ℤ :=
  ∑ i, (∑ l, τ.cartan i l * β l) * ((k i).val : ℤ)

theorem Nexp_cast (τ : Tag) (k : Fin τ.rank → ZMod 11) (β : Fin τ.rank → ℤ) :
    ((Nexp τ k β : ℤ) : ZMod 11) = ∑ i, k i * wt τ 11 β i := by
  have hw : ∀ i, wt τ 11 β i = ∑ l, ((τ.cartan i l : ℤ) : ZMod 11) * ((β l : ℤ) : ZMod 11) :=
    fun i => rfl
  unfold Nexp
  push_cast
  simp only [ZMod.natCast_zmod_val, hw]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

theorem iotaM_coeff_root {τ : Tag} {K : Type} [Field K] (ζ : Kˣ) (k : Fin τ.rank → ZMod 11)
    (β : Fin τ.rank → ℤ) (hβ : IsRoot τ β) :
    ((iotaM τ K ζ k : Module.End K (RootModule τ K)) (Finsupp.single (Sum.inr ⟨β, hβ⟩) 1))
      (Sum.inr ⟨β, hβ⟩) = ((ζ ^ Nexp τ k β : Kˣ) : K) := by
  have hr : rootVec τ K β (Sum.inr ⟨β, hβ⟩) = 1 := by
    rw [rootVec_eq_single_of_isRoot hβ, Finsupp.single_eq_same]
  rw [← rootVec_eq_single_of_isRoot hβ, iotaM_rootVec ζ k β hβ, Finsupp.smul_apply, hr,
    smul_eq_mul, mul_one]
  exact prod_zpow_pow_coe ζ (fun i => ∑ l, τ.cartan i l * β l) (fun i => (k i).val)

theorem iotaM_coeff_hVec {τ : Tag} {K : Type} [Field K] (ζ : Kˣ) (k : Fin τ.rank → ZMod 11)
    (i : Fin τ.rank) :
    ((iotaM τ K ζ k : Module.End K (RootModule τ K)) (Finsupp.single (Sum.inl i) 1))
      (Sum.inl i) = 1 := by
  have h : (iotaM τ K ζ k : Module.End K (RootModule τ K)) (Finsupp.single (Sum.inl i) 1) =
      Finsupp.single (Sum.inl i) 1 := iotaM_hVec ζ k i
  rw [h, Finsupp.single_eq_same]

theorem zpow_val_pow_eleven {K : Type} [Field K] {ζ : Kˣ} (hζ : orderOf ζ = 11) (N : ℤ) :
    (((ζ ^ N : Kˣ) : K)) ^ 11 = 1 := by
  have hz11 : ζ ^ 11 = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    hz11, one_zpow]
  rfl

theorem iotaM_pow_eleven {τ : Tag} {K : Type} [Field K] {ζ : Kˣ} (hζ : orderOf ζ = 11)
    (k : Fin τ.rank → ZMod 11) : iotaM τ K ζ k ^ 11 = 1 := by
  apply units_eq_one_of_basis
  intro a
  have hT := iotaM_mem (τ := τ) (K := K) ζ k
  rw [units_pow_apply_of_eigen (iotaM τ K ζ k) _ _ (torus_single_eq hT a) 11]
  have hc : ((((iotaM τ K ζ k : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single a 1))
      a) ^ 11 = 1 := by
    rcases a with i | ⟨β, hβ⟩
    · rw [iotaM_coeff_hVec]
      simp
    · rw [iotaM_coeff_root]
      exact zpow_val_pow_eleven hζ _
  rw [hc, one_smul]

end Torus

theorem zpow_val_eq_iff {K : Type} [Field K] {ζ : Kˣ} (hζ : orderOf ζ = 11) (N M : ℤ) :
    ((ζ ^ N : Kˣ) : K) = ((ζ ^ M : Kˣ) : K) ↔ ((N : ℤ) : ZMod 11) = ((M : ℤ) : ZMod 11) := by
  rw [Units.val_inj, zpow_eq_zpow_iff_modEq, hζ]
  have := ZMod.intCast_eq_intCast_iff N M 11
  simpa using this.symm

section Main


noncomputable def iotaG (τ : Tag) (K : Type) [Field K] [Finite K] (ζ : Kˣ)
    (k : Fin τ.rank → ZMod 11) : ↥(adjointGroup τ K) :=
  ⟨iotaM τ K ζ k,
    CFSG.LocalAnalysis.RankFourTheoremC.crossExc_torusGroup_le_adjointGroup (iotaM_mem ζ k)⟩

theorem sylow_hN {τ : Tag} (hτ : τ = .G2 ∨ τ = .D4 ∨ τ = .F4)
    {K : Type} [Field K] [Finite K] {ζ : Kˣ} (hζ : orderOf ζ = 11)
    (P : Sylow 11 ↥(adjointGroup τ K))
    (hPD : (P : Subgroup ↥(adjointGroup τ K)) ≤ (torusGroup τ K).subgroupOf (adjointGroup τ K))
    {u : ↥(adjointGroup τ K)}
    (hu : u ∈ Subgroup.normalizer ((P : Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K))) :
    u ^ (if τ = .G2 then 6 else 24) ∈
      Subgroup.centralizer ((P : Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)) := by
  classical
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  haveI : Finite (ModGL τ K) := finite_modGL
  letI : Fintype (Label τ) := Fintype.ofFinite _
  let ρ : ↥(adjointGroup τ K) →* Module.End K (RootModule τ K) :=
    (Units.coeHom (Module.End K (RootModule τ K))).comp (adjointGroup τ K).subtype
  have hρ : Function.Injective ρ := fun x y h => Subtype.ext (Units.ext h)
  let b : Module.Basis (Label τ) K (RootModule τ K) := Finsupp.basisSingleOne
  have hb : ∀ a, b a = Finsupp.single a 1 := fun a => by simp [b]
  let χ : Label τ → ↥(adjointGroup τ K) → K := fun a x => ρ x (Finsupp.single a 1) a
  have hxT : ∀ x ∈ (P : Subgroup ↥(adjointGroup τ K)),
      ((x : ↥(adjointGroup τ K)) : ModGL τ K) ∈ torusGroup τ K :=
    fun x hx => Subgroup.mem_subgroupOf.1 (hPD hx)
  have hχ : ∀ x ∈ (P : Subgroup ↥(adjointGroup τ K)), ∀ a, ρ x (b a) = χ a x • b a := by
    intro x hx a
    rw [hb a]
    exact torus_single_eq (hxT x hx) a
  have hχinl : ∀ x ∈ (P : Subgroup ↥(adjointGroup τ K)), ∀ i : Fin τ.rank, χ (Sum.inl i) x = 1 := by
    intro x hx i
    obtain ⟨θ, hfix, -⟩ := torus_mem_char (hxT x hx)
    show (((x : ↥(adjointGroup τ K)) : ModGL τ K) : Module.End K (RootModule τ K))
      (Finsupp.single (Sum.inl i) 1) (Sum.inl i) = 1
    have h1 : (((x : ↥(adjointGroup τ K)) : ModGL τ K) : Module.End K (RootModule τ K))
        (Finsupp.single (Sum.inl i) 1) = Finsupp.single (Sum.inl i) 1 := hfix i
    rw [h1, Finsupp.single_eq_same]
  have hcomm : ∀ a ∈ (torusGroup τ K).subgroupOf (adjointGroup τ K),
      ∀ c ∈ (torusGroup τ K).subgroupOf (adjointGroup τ K), a * c = c * a := by
    intro a ha c hc
    exact Subtype.ext ((triangular_borel_structure.{0, 0} τ K).1 _
      (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hc))
  have hiotaD : ∀ k, iotaG τ K ζ k ∈ (torusGroup τ K).subgroupOf (adjointGroup τ K) :=
    fun k => Subgroup.mem_subgroupOf.2 (iotaM_mem ζ k)
  have hiota11 : ∀ k, iotaG τ K ζ k ^ 11 = 1 := by
    intro k
    apply Subtype.ext
    rw [SubgroupClass.coe_pow]
    exact iotaM_pow_eleven hζ k
  have hiotaR : ∀ k, iotaG τ K ζ k ∈ (P : Subgroup ↥(adjointGroup τ K)) := fun k =>
    sylow_mem_of_comm P hPD hcomm (hiotaD k) (zpowers_isPGroup_of_pow (hiota11 k))
  have hchi_root : ∀ k (β : Fin τ.rank → ℤ) (hβ : IsRoot τ β),
      χ (Sum.inr ⟨β, hβ⟩) (iotaG τ K ζ k) = ((ζ ^ Nexp τ k β : Kˣ) : K) := fun k β hβ =>
    iotaM_coeff_root ζ k β hβ
  have hnontriv : ∀ β : {v : Fin τ.rank → ℤ // IsRoot τ v}, ∃ k : Fin τ.rank → ZMod 11,
      χ (Sum.inr β) (iotaG τ K ζ k) ≠ 1 := by
    intro β
    obtain ⟨i0, hi0⟩ : ∃ i0, wt τ 11 β.1 i0 ≠ 0 := by
      by_contra h
      push Not at h
      exact wt_ne_zero hτ β.2 (funext h)
    refine ⟨Pi.single i0 1, ?_⟩
    rw [hchi_root]
    intro h
    have h0 : ((ζ ^ Nexp τ (Pi.single i0 1) β.1 : Kˣ) : K) = ((ζ ^ (0 : ℤ) : Kˣ) : K) := by
      rw [zpow_zero, Units.val_one]
      exact h
    rw [zpow_val_eq_iff hζ, Nexp_cast] at h0
    simp [Pi.single_apply] at h0
    exact hi0 (by simpa using h0)
  have hπ0 : ∀ β : {v : Fin τ.rank → ℤ // IsRoot τ v}, ∃ γ : {v : Fin τ.rank → ℤ // IsRoot τ v},
      ∀ x ∈ (P : Subgroup ↥(adjointGroup τ K)),
        χ (Sum.inr γ) x = χ (Sum.inr β) (u⁻¹ * x * u) := by
    intro β
    obtain ⟨j, hj⟩ := eigen_conj_exists hχ hu (Sum.inr β)
    rcases j with i | γ
    · exfalso
      obtain ⟨k0, hk0⟩ := hnontriv β
      have hmem := conj_mem_of_mem_normalizer hu (hiotaR k0)
      have h1 := hj (u * iotaG τ K ζ k0 * u⁻¹) hmem
      rw [hχinl _ hmem i] at h1
      apply hk0
      rw [show u⁻¹ * (u * iotaG τ K ζ k0 * u⁻¹) * u = iotaG τ K ζ k0 by group] at h1
      exact h1.symm
    · exact ⟨γ, hj⟩
  choose π hπ using hπ0
  have hyK : ∀ k : Fin τ.rank → ZMod 11, ∃ k' : Fin τ.rank → ZMod 11,
      ((u⁻¹ * iotaG τ K ζ k * u : ↥(adjointGroup τ K)) : ModGL τ K) = iotaM τ K ζ k' := by
    intro k
    have hmem : u⁻¹ * iotaG τ K ζ k * u ∈ (P : Subgroup ↥(adjointGroup τ K)) :=
      conj_inv_mem_of_mem_normalizer hu (hiotaR k)
    have hT := hxT _ hmem
    have hpow11 : (u⁻¹ * iotaG τ K ζ k * u) ^ 11 = 1 := by
      have h := conj_pow (a := u⁻¹) (b := iotaG τ K ζ k) (i := 11)
      simp only [inv_inv] at h
      rw [h, hiota11 k]
      group
    have h11 : ((u⁻¹ * iotaG τ K ζ k * u : ↥(adjointGroup τ K)) : ModGL τ K) ^ 11 = 1 := by
      rw [← SubgroupClass.coe_pow, hpow11]
      rfl
    obtain ⟨k', hk'⟩ := omega_one_torusGroup_eq hζ hT h11
    exact ⟨k', hk'⟩
  choose Mf hMf using hyK
  have hel : ∀ k, u⁻¹ * iotaG τ K ζ k * u = iotaG τ K ζ (Mf k) := fun k => Subtype.ext (hMf k)
  have hstar : ∀ (β : {v : Fin τ.rank → ℤ // IsRoot τ v}) (k : Fin τ.rank → ZMod 11),
      ∑ i, k i * wt τ 11 (π β).1 i = ∑ i, Mf k i * wt τ 11 β.1 i := by
    intro β k
    have h3 : ((ζ ^ Nexp τ k (π β).1 : Kˣ) : K) = ((ζ ^ Nexp τ (Mf k) β.1 : Kˣ) : K) := by
      calc ((ζ ^ Nexp τ k (π β).1 : Kˣ) : K)
          = χ (Sum.inr (π β)) (iotaG τ K ζ k) := (hchi_root k (π β).1 (π β).2).symm
        _ = χ (Sum.inr β) (u⁻¹ * iotaG τ K ζ k * u) := hπ β _ (hiotaR k)
        _ = χ (Sum.inr β) (iotaG τ K ζ (Mf k)) := by rw [hel k]
        _ = ((ζ ^ Nexp τ (Mf k) β.1 : Kˣ) : K) := hchi_root (Mf k) β.1 β.2
    have h4 := (zpow_val_eq_iff hζ _ _).1 h3
    rw [Nexp_cast, Nexp_cast] at h4
    exact h4
  let Bm : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 11) :=
    Matrix.of fun j i => Mf (Pi.single j 1) i
  have hBm : ∀ β : {v : Fin τ.rank → ℤ // IsRoot τ v},
      Matrix.mulVec Bm (wt τ 11 β.1) = wt τ 11 (π β).1 := by
    intro β
    funext j
    have h := hstar β (Pi.single j 1)
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at h
    simp only [Matrix.mulVec, dotProduct, Bm, Matrix.of_apply]
    exact h.symm
  have hB : ∀ β : Fin τ.rank → ℤ, IsRoot τ β →
      ∃ γ, IsRoot τ γ ∧ Matrix.mulVec Bm (wt τ 11 β) = wt τ 11 γ := fun β hβ =>
    ⟨(π ⟨β, hβ⟩).1, (π ⟨β, hβ⟩).2, hBm ⟨β, hβ⟩⟩
  have hBpow : Bm ^ (if τ = .G2 then 6 else 24) = 1 := rootWeight_stab_pow τ hτ Bm hB
  have hwπ : ∀ (n : ℕ) (β : {v : Fin τ.rank → ℤ // IsRoot τ v}),
      wt τ 11 ((π^[n]) β).1 = Matrix.mulVec (Bm ^ n) (wt τ 11 β.1) := by
    intro n
    induction n with
    | zero => intro β; simp
    | succ n ih =>
      intro β
      rw [Function.iterate_succ_apply, ih (π β), ← hBm β, Matrix.mulVec_mulVec, ← pow_succ]
  have hπe : ∀ β : {v : Fin τ.rank → ℤ // IsRoot τ v}, (π^[if τ = .G2 then 6 else 24]) β = β := by
    intro β
    apply Subtype.ext
    apply wt_eq_imp_eq hτ ((π^[if τ = .G2 then 6 else 24]) β).2 β.2
    rw [hwπ, hBpow, Matrix.one_mulVec]
  have hpow : ∀ n : ℕ, ∀ y ∈ (P : Subgroup ↥(adjointGroup τ K)),
      (u ^ n)⁻¹ * y * u ^ n ∈ (P : Subgroup ↥(adjointGroup τ K)) := fun n y hy =>
    conj_inv_mem_of_mem_normalizer (pow_mem hu n) hy
  have hiter : ∀ (n : ℕ) (β : {v : Fin τ.rank → ℤ // IsRoot τ v}) (y : ↥(adjointGroup τ K)),
      y ∈ (P : Subgroup ↥(adjointGroup τ K)) →
      χ (Sum.inr ((π^[n]) β)) y = χ (Sum.inr β) ((u ^ n)⁻¹ * y * u ^ n) := by
    intro n
    induction n with
    | zero => intro β y hy; simp
    | succ n ih =>
      intro β y hy
      rw [Function.iterate_succ_apply, ih (π β) y hy, hπ β _ (hpow n y hy)]
      congr 1
      rw [pow_succ]
      group
  have hfix : ∀ (β : {v : Fin τ.rank → ℤ // IsRoot τ v}) (y : ↥(adjointGroup τ K)),
      y ∈ (P : Subgroup ↥(adjointGroup τ K)) →
      χ (Sum.inr β) ((u ^ (if τ = .G2 then 6 else 24))⁻¹ * y * u ^ (if τ = .G2 then 6 else 24)) =
        χ (Sum.inr β) y := by
    intro β y hy
    have h := hiter (if τ = .G2 then 6 else 24) β y hy
    rw [hπe β] at h
    exact h.symm
  have hc : ∀ a : Label τ, ∀ y ∈ (P : Subgroup ↥(adjointGroup τ K)),
      χ a ((u ^ (if τ = .G2 then 6 else 24))⁻¹ * y * u ^ (if τ = .G2 then 6 else 24)) =
        χ a y := by
    intro a y hy
    rcases a with i | β
    · rw [hχinl _ (hpow _ y hy) i, hχinl _ hy i]
    · exact hfix β y hy
  exact eigen_mem_centralizer_of_char hρ hχ (pow_mem hu _) hc

theorem sylowAutBoundAll_adjointGroup_split {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .D4 ∨ τ = .F4) {K : Type} [Field K] [Finite K]
    (hK : 11 ∣ Nat.card K - 1) :
    SylowAutBoundAll 11 (if τ = .G2 then 6 else 24) (adjointGroup τ K) := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  haveI : Finite (ModGL τ K) := finite_modGL
  have hunits : 11 ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hK
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 11 hunits
  have hW : ¬ 11 ∣ Nat.card (WeylGroup τ) := by
    rcases hτ with rfl | rfl | rfl
    · rw [CFSG.RankThree.PartOne.K133H.card_weylGroup_G2]
      norm_num
    · exact CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 (by norm_num) (by norm_num)
    · rw [CFSG.RankThree.PartOne.K133H.card_weylGroup_F4]
      norm_num
  apply SylowAutBoundAll.of_abelian_index (D := (torusGroup τ K).subgroupOf (adjointGroup τ K))
  · intro a ha c hc
    exact Subtype.ext ((triangular_borel_structure.{0, 0} τ K).1 _
      (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hc))
  · exact CFSG.LocalAnalysis.RankFourTheoremC.crossExc_not_dvd_index_torusGroup (p := 11)
      (by norm_num) hW hK
  · intro P hPD u hu
    exact sylow_hN hτ hζ P hPD hu

theorem sylowAutBoundAll_adjointGroup {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .D4 ∨ τ = .F4) {K : Type} [Field K] [Finite K] (hK : ¬ 11 ∣ Nat.card K) :
    SylowAutBoundAll 11 (if τ = .G2 then 6 else 24) (adjointGroup τ K) := by
  classical
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  haveI : Finite (ModGL τ K) := finite_modGL
  obtain ⟨ℓ, hℓ⟩ := CharP.exists K
  haveI : CharP K ℓ := hℓ
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hℓp, -⟩ := FiniteField.card K ℓ
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  letI : Algebra (ZMod ℓ) K := ZMod.algebra K ℓ
  set f := Module.finrank (ZMod ℓ) K with hf
  have hKf : ℓ ^ f = Nat.card K := FiniteField.pow_finrank_eq_natCard ℓ K
  have hf0 : f ≠ 0 := Module.finrank_pos.ne'
  have hm0 : 11 - 1 ≠ 0 := by norm_num
  have hfm : f * (11 - 1) ≠ 0 := Nat.mul_ne_zero hf0 hm0
  have hK' : Nat.card (GaloisField ℓ (f * (11 - 1))) = Nat.card K ^ (11 - 1) := by
    rw [GaloisField.card ℓ (f * (11 - 1)) hfm, pow_mul, hKf]
  have hdvd : 11 ∣ Nat.card (GaloisField ℓ (f * (11 - 1))) - 1 := by
    rw [hK']
    exact CFSG.LocalAnalysis.RankFourTheoremC.crossExc_dvd_pow_pred_sub_one (by norm_num) hK
  obtain ⟨ι⟩ : Nonempty (K →ₐ[ZMod ℓ] GaloisField ℓ (f * (11 - 1))) :=
    FiniteField.nonempty_algHom_of_finrank_dvd (by
      rw [GaloisField.finrank ℓ hfm]
      exact dvd_mul_right f _)
  have hle : (adjointGroup τ K).map (baseChangeGL ι.toRingHom) ≤
      adjointGroup τ (GaloisField ℓ (f * (11 - 1))) := by
    rw [map_baseChangeGL_adjointGroup, Subgroup.closure_le]
    rintro _ ⟨i, c, rfl | rfl⟩
    exacts [xUnit_mem_adjointGroup i _, yUnit_mem_adjointGroup i _]
  let φ : adjointGroup τ K →* adjointGroup τ (GaloisField ℓ (f * (11 - 1))) :=
    ((baseChangeGL ι.toRingHom).comp (adjointGroup τ K).subtype).codRestrict _
      fun g => hle (Subgroup.mem_map_of_mem _ g.2)
  have hφ : Function.Injective φ := fun a b h =>
    Subtype.ext (baseChangeGL_injective ι.toRingHom (congrArg Subtype.val h))
  haveI : Finite (ModGL τ (GaloisField ℓ (f * (11 - 1)))) := finite_modGL
  exact SylowAutBoundAll.of_injective φ hφ (sylowAutBoundAll_adjointGroup_split hτ hdvd)

end Main

end CFSG.Quasithin.KGC31
