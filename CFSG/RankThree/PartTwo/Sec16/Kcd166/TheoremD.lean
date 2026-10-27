module

public import CFSG.RankThree.PartTwo.Sec16.Kcd166.NoKleinCore
public import CFSG.RankThree.PartTwo.Sec16.Kcd166.SmallDim
public import CFSG.RankThree.PartTwo.Sec16.Kcd166.TheoremC
public import CFSG.RankThree.PartTwo.Sec16.Kcd166.TheoremB
public import CFSG.RankThree.PartTwo.Sec16.Kcd166.GFlat
public import CFSG.RankThree.PartOne.S10.EmbeddingTransport

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open CFSG.RankThree.PartTwo

private def cyc012 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

private def cyc345 : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

private theorem cyc012_pow_three : cyc012 ^ 3 = 1 := by decide

private theorem cyc345_pow_three : cyc345 ^ 3 = 1 := by decide

private theorem cyc012_ne_one : cyc012 ≠ 1 := by decide

private theorem cyc345_ne_one : cyc345 ≠ 1 := by decide

private theorem cyc012_mul_cyc345 : cyc012 * cyc345 = cyc345 * cyc012 := by decide

private theorem sign_cyc012 : Equiv.Perm.sign cyc012 = 1 := by
  rw [cyc012, map_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  rfl

private theorem sign_cyc345 : Equiv.Perm.sign cyc345 = 1 := by
  rw [cyc345, map_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  rfl

private def alt012 : alternatingGroup (Fin 6) :=
  ⟨cyc012, Equiv.Perm.mem_alternatingGroup.mpr sign_cyc012⟩

private def alt345 : alternatingGroup (Fin 6) :=
  ⟨cyc345, Equiv.Perm.mem_alternatingGroup.mpr sign_cyc345⟩

private theorem alt012_mul_alt345 : alt012 * alt345 = alt345 * alt012 :=
  Subtype.ext cyc012_mul_cyc345

private theorem orderOf_alt012 : orderOf alt012 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← Subgroup.orderOf_coe]
  exact orderOf_eq_prime cyc012_pow_three cyc012_ne_one

private theorem orderOf_alt345 : orderOf alt345 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← Subgroup.orderOf_coe]
  exact orderOf_eq_prime cyc345_pow_three cyc345_ne_one

private def fixThree : Subgroup (alternatingGroup (Fin 6)) where
  carrier := {x | (x : Equiv.Perm (Fin 6)) 3 = 3}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    show ((a : Equiv.Perm (Fin 6)) * (b : Equiv.Perm (Fin 6))) 3 = 3
    rw [Equiv.Perm.mul_apply, hb]
    exact ha
  inv_mem' := by
    intro a ha
    refine (a : Equiv.Perm (Fin 6)).injective ?_
    show (a : Equiv.Perm (Fin 6)) ((a : Equiv.Perm (Fin 6))⁻¹ 3) =
      (a : Equiv.Perm (Fin 6)) 3
    rw [ha]
    simp

private theorem alt012_mem_fixThree : alt012 ∈ fixThree := by
  show cyc012 3 = 3
  decide

private theorem alt345_not_mem_fixThree : alt345 ∉ fixThree := by
  show cyc345 3 ≠ 3
  decide

private theorem zpowers_alt345_le_normalizer :
    Subgroup.zpowers alt345 ≤ Subgroup.normalizer (Subgroup.zpowers alt012) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff_map_conj_eq]
  have h1 : (MulAut.conj alt345 : alternatingGroup (Fin 6) →* alternatingGroup (Fin 6))
      alt012 = alt012 := by
    show alt345 * alt012 * alt345⁻¹ = alt012
    rw [← alt012_mul_alt345]
    group
  rw [MonoidHom.map_zpowers, h1]

private theorem isPGroup_zpowers_alt012 : IsPGroup 3 (Subgroup.zpowers alt012) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_alt012]; norm_num)

private theorem isPGroup_zpowers_alt345 : IsPGroup 3 (Subgroup.zpowers alt345) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_alt345]; norm_num)

private def p3 : Subgroup (alternatingGroup (Fin 6)) :=
  Subgroup.zpowers alt012 ⊔ Subgroup.zpowers alt345

private theorem isPGroup_p3 : IsPGroup 3 p3 :=
  IsPGroup.to_sup_of_normal_left' isPGroup_zpowers_alt012 isPGroup_zpowers_alt345
    zpowers_alt345_le_normalizer

private theorem not_isCyclic_p3 : ¬ IsCyclic p3 := by
  intro hcyc
  haveI := hcyc
  have hmem12 : alt012 ∈ Subgroup.zpowers alt012 ⊔ Subgroup.zpowers alt345 :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers alt012)
  have hmem45 : alt345 ∈ Subgroup.zpowers alt012 ⊔ Subgroup.zpowers alt345 :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers alt345)
  let s' : ↥p3 := ⟨alt012, hmem12⟩
  let t' : ↥p3 := ⟨alt345, hmem45⟩
  have hs' : Nat.card (Subgroup.zpowers s') = 3 := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    exact orderOf_alt012
  have ht' : Nat.card (Subgroup.zpowers t') = 3 := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    exact orderOf_alt345
  have hcard : Nat.card (Subgroup.zpowers s') = Nat.card (Subgroup.zpowers t') := by
    rw [hs', ht']
  have heq : Subgroup.zpowers s' = Subgroup.zpowers t' :=
    (IsCyclic.subgroup_eq_iff_card_eq).mpr hcard
  have htmem : t' ∈ Subgroup.zpowers s' := heq.symm ▸ Subgroup.mem_zpowers t'
  have hsub : Subgroup.zpowers s' ≤ fixThree.subgroupOf p3 := by
    rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
    exact alt012_mem_fixThree
  exact alt345_not_mem_fixThree (hsub htmem)

private theorem exists_noncyclic_three_of_surjective {G : Type*} [Group G] [Finite G]
    {f : G →* alternatingGroup (Fin 6)} (hf : Function.Surjective f) :
    ∃ P : Subgroup G, IsPGroup 3 P ∧ ¬ IsCyclic P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T₀, hT₀⟩ := isPGroup_p3.exists_le_sylow
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hf 3 T₀
  refine ⟨S, S.isPGroup', fun hcyc => not_isCyclic_p3 ?_⟩
  have hSmap : ((S : Subgroup G)).map f = (T₀ : Subgroup (alternatingGroup (Fin 6))) := by
    rw [← Sylow.coe_mapSurjective (f := f) hf S, hS]
  haveI := hcyc
  have hcyc' : IsCyclic ↥(((S : Subgroup G)).map f) :=
    isCyclic_of_surjective (f.subgroupMap (S : Subgroup G))
      (f.subgroupMap_surjective (S : Subgroup G))
  rw [hSmap] at hcyc'
  haveI : IsCyclic ↥(T₀ : Subgroup (alternatingGroup (Fin 6))) := hcyc'
  exact isCyclic_of_injective (Subgroup.inclusion hT₀) (Subgroup.inclusion_injective hT₀)

private theorem exists_noncyclic_three_kerRepresentation {𝕜 : Type*} [Field 𝕜]
    {K : Type} [Group K] [Finite K] {W : Type*} [AddCommGroup W] [Module 𝕜 W]
    (ρ : Representation 𝕜 K W) {T : Type} [Group T] (π : K →* T)
    (hπ : Function.Surjective π) (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hρπ : ρ.ker ≤ π.ker) :
    ∃ P : Subgroup (K ⧸ ρ.ker), IsPGroup 3 P ∧ ¬ IsCyclic P := by
  obtain ⟨e⟩ := hT.2
  let f : K ⧸ ρ.ker →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center T)).comp
      (QuotientGroup.lift ρ.ker π hρπ))
  have hf : Function.Surjective f :=
    e.surjective.comp ((QuotientGroup.mk'_surjective (Subgroup.center T)).comp
      (QuotientGroup.lift_surjective_of_surjective (N := ρ.ker) π hπ hρπ))
  exact exists_noncyclic_three_of_surjective hf

private theorem lift_ker_data {𝕜 : Type*} [Field 𝕜] {K : Type} [Group K] [Finite K]
    {W : Type*} [AddCommGroup W] [Module 𝕜 W] (ρ : Representation 𝕜 K W)
    {T : Type} [Group T] (π : K →* T) (hπ : Function.Surjective π)
    (hker3 : Nat.Coprime (Nat.card π.ker) 3) (hkerS : Group.IsSolvable π.ker)
    (hρπ : ρ.ker ≤ π.ker) :
    Function.Surjective (QuotientGroup.lift ρ.ker π hρπ) ∧
      Nat.Coprime (Nat.card (QuotientGroup.lift ρ.ker π hρπ).ker) 3 ∧
      Group.IsSolvable ↥(QuotientGroup.lift ρ.ker π hρπ).ker ∧
      (QuotientGroup.lift ρ.ker π hρπ).comp (QuotientGroup.mk' ρ.ker) = π := by
  haveI : ρ.ker.Normal := MonoidHom.normal_ker ρ
  refine ⟨QuotientGroup.lift_surjective_of_surjective (N := ρ.ker) π hπ hρπ, ?_, ?_, ?_⟩
  · rw [QuotientGroup.ker_lift (N := ρ.ker) π hρπ]
    exact hker3.coprime_dvd_left
      (Subgroup.card_map_dvd (H := π.ker) (QuotientGroup.mk' ρ.ker))
  · rw [QuotientGroup.ker_lift (N := ρ.ker) π hρπ]
    haveI : Group.IsSolvable ↥π.ker := hkerS
    exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' ρ.ker).subgroupMap π.ker)
      ((QuotientGroup.mk' ρ.ker).subgroupMap_surjective π.ker)
  · ext k
    exact QuotientGroup.lift_mk' (N := ρ.ker) (φ := π) hρπ k

theorem eq_zero_of_finrank_le_three {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜] {p : ℕ} [CharP 𝕜 p]
    (hp : p.Prime) (hp5 : 5 ≤ p)
    {K : Type} [Group K] [Finite K] (hperf : Group.IsPerfect K)
    {W : Type*} [AddCommGroup W] [Module 𝕜 W] [FiniteDimensional 𝕜 W]
    (hW : Module.finrank 𝕜 W ≤ 3) (ρ : Representation 𝕜 K W)
    {T : Type} [Group T] (π : K →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hker3 : Nat.Coprime (Nat.card π.ker) 3) (hkerS : Group.IsSolvable π.ker)
    (hρπ : ρ.ker ≤ π.ker)
    {J : Subgroup K} (hJ : Nonempty (↥(J.map π) ≃* alternatingGroup (Fin 5)))
    {w : W} (hw : ∀ g ∈ J, ρ g w = w) : w = 0 := by
  classical
  have h2 : (2 : 𝕜) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : 𝕜) = 0 := by exact_mod_cast h0
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff 𝕜 p 2).1 h0'
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have h3 : (3 : 𝕜) ≠ 0 := by
    intro h0
    have h0' : ((3 : ℕ) : 𝕜) = 0 := by exact_mod_cast h0
    have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff 𝕜 p 3).1 h0'
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have h6 : (6 : 𝕜) ≠ 0 := by
    have hsplit : (6 : 𝕜) = 2 * 3 := by norm_num
    rw [hsplit]
    exact mul_ne_zero h2 h3
  haveI : Group.IsPerfect K := hperf
  let ρb : Representation 𝕜 (K ⧸ ρ.ker) W := CFSG.Theory.Representation.kerRepresentation ρ
  let πb : K ⧸ ρ.ker →* T := QuotientGroup.lift ρ.ker π hρπ
  obtain ⟨hπb, hker3b, hkerSb, hπb_comp⟩ := lift_ker_data ρ π hπ hker3 hkerS hρπ
  have hfaith : Function.Injective ρb :=
    CFSG.Theory.Representation.kerRepresentation_faithful (ρ := ρ)
  have hperfb : Group.IsPerfect (K ⧸ ρ.ker) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective ρ.ker)
  obtain ⟨P, hP, hPc⟩ := exists_noncyclic_three_kerRepresentation ρ π hπ hT hρπ
  obtain ⟨hirr, hdim⟩ := isIrreducible_and_finrank_eq_three h3 hperfb hW ρb hfaith hP hPc
  have hr3b : ∀ t : K ⧸ ρ.ker, IsPGroup 2 (Subgroup.zpowers t) → t ≠ 1 →
      Module.finrank 𝕜 (LinearMap.ker (ρb t - 1)) ≤ 3 :=
    fun t _ _ => (Submodule.finrank_le _).trans hdim.le
  have hr3c : ∀ t : K ⧸ ρ.ker, t ^ 2 = 1 → t ≠ 1 →
      Module.finrank 𝕜 (LinearMap.ker (ρb t - 1)) ≤ 3 :=
    fun t _ _ => (Submodule.finrank_le _).trans hdim.le
  have hKcenter : πb.ker ≤ Subgroup.center (K ⧸ ρ.ker) :=
    ker_le_center_of_finrank_le_nine hp hp5 hperfb ρb hirr hfaith (by rw [hdim]; norm_num)
      πb hπb hT hker3b hkerSb hr3b
  have hJb : Nonempty (↥((J.map (QuotientGroup.mk' ρ.ker)).map πb) ≃*
      alternatingGroup (Fin 5)) := by
    rw [Subgroup.map_map, hπb_comp]
    exact hJ
  refine eq_zero_of_ker_le_center h6 hperfb ρb hirr hfaith πb hπb hT hKcenter hker3b hr3c
    hJb ?_
  intro g hg
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hg
  exact hw j hj

private theorem exists_noKlein_data {Γ T : Type*} [Group Γ] [Finite Γ] [Group T]
    (hperf : Group.IsPerfect Γ)
    (hno : ∀ s t : Γ, s ^ 2 = 1 → t ^ 2 = 1 → s ≠ 1 → t ≠ 1 → s * t = t * s → s = t)
    (π : Γ →* T) (hker3 : Nat.Coprime (Nat.card π.ker) 3)
    (hkerS : Group.IsSolvable π.ker) {d : Γ} (hd3 : d ^ 3 = 1)
    {I : Subgroup Γ} (hIperf : Group.IsPerfect I)
    (hIA5 : Nonempty (↥(I.map π) ≃* alternatingGroup (Fin 5)))
    (hI2 : IsPGroup 2 ↥(I ⊓ π.ker)) (hId : I ≤ Subgroup.centralizer ({d} : Set Γ)) :
    ∃ (z : Γ) (O K₀ : Subgroup Γ), z ∈ I ∧ z ^ 2 = 1 ∧ z ≠ 1 ∧
      O.Normal ∧ O ≤ π.ker ∧ K₀ ⊔ O = ⊤ ∧ Group.IsPerfect ↥K₀ ∧
      K₀ ≤ Subgroup.centralizer ({z} : Set Γ) ∧ d ∈ K₀ ∧ I ≤ K₀ := by
  classical
  haveI : Group.IsPerfect Γ := hperf
  haveI hπn : π.ker.Normal := MonoidHom.normal_ker π
  obtain ⟨z, hzK, hz2, hz1, hIz⟩ := exists_involution_mem_inf_ker π hno hIA5 hI2
  obtain ⟨O, hOn, hOle, _, _, hCsup⟩ :=
    exists_odd_normal_centralizer_sup_eq_top hno (MonoidHom.normal_ker π) hkerS hzK.2 hz2 hz1
  haveI : O.Normal := hOn
  have hO3 : Nat.Coprime (Nat.card O) 3 :=
    hker3.coprime_dvd_left (Subgroup.card_dvd_of_le hOle)
  have hdC : d ∈ Subgroup.centralizer ({z} : Set Γ) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hId hzK.1)).symm
  obtain ⟨hK0sup, hdK0⟩ :=
    mem_perfectResidual_of_sup_eq_top (C := Subgroup.centralizer ({z} : Set Γ)) hperf hOn hCsup hO3
  have hK0perf : Group.IsPerfect
      ↥(CFSG.inSubgroup CFSG.perfectResidual (Subgroup.centralizer ({z} : Set Γ))) := by
    have h := (CFSG.perfect_residual_characterization
      (G := ↥(Subgroup.centralizer ({z} : Set Γ)))).2.2.1
    exact Group.IsPerfect.map (Subgroup.centralizer ({z} : Set Γ)).subtype
  exact ⟨z, O, _, hzK.1, hz2, hz1, hOn, hOle, hK0sup, hK0perf,
    Subgroup.map_subtype_le _, hdK0 d hdC hd3,
    CFSG.RankThree.PartOne.EmbeddingTransport.le_inSubgroup_perfectResidual_of_isPerfect
      hIz hIperf⟩

private theorem ker_comp_subtype_data {Γ T : Type*} [Group Γ] [Finite Γ] [Group T]
    (π : Γ →* T) {K₀ : Subgroup Γ} (hker3 : Nat.Coprime (Nat.card π.ker) 3)
    (hkerS : Group.IsSolvable π.ker) :
    Nat.Coprime (Nat.card ↥(π.comp K₀.subtype).ker) 3 ∧
      Group.IsSolvable ↥(π.comp K₀.subtype).ker := by
  let inc : ↥(π.comp K₀.subtype).ker →* ↥π.ker :=
    { toFun := fun x => ⟨(x.1 : Γ), x.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  have hinc : Function.Injective inc := by
    intro a b h
    have h' : ((a : ↥K₀) : Γ) = ((b : ↥K₀) : Γ) :=
      congrArg (fun y : ↥π.ker => (y : Γ)) h
    exact Subtype.ext (Subtype.ext h')
  refine ⟨hker3.coprime_dvd_left (Subgroup.card_dvd_of_injective inc hinc), ?_⟩
  haveI : Group.IsSolvable ↥π.ker := hkerS
  exact Group.isSolvable_of_isSolvable_injective hinc

private theorem surjective_comp_subtype {Γ T : Type*} [Group Γ] [Group T]
    {π : Γ →* T} (hπ : Function.Surjective π) {K₀ O : Subgroup Γ} (hO : O.Normal)
    (hOle : O ≤ π.ker) (hsup : K₀ ⊔ O = ⊤) :
    Function.Surjective (π.comp K₀.subtype) := by
  haveI : O.Normal := hO
  intro t
  obtain ⟨g, rfl⟩ := hπ t
  have hg : g ∈ K₀ ⊔ O := by rw [hsup]; exact Subgroup.mem_top g
  obtain ⟨k, hk, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  refine ⟨⟨k, hk⟩, ?_⟩
  show π k = π (k * o)
  rw [map_mul]
  have ho1 : π o = 1 := by
    have ho' : o ∈ π.ker := hOle ho
    simpa using ho'
  rw [ho1, mul_one]

private theorem exists_restrict_representation {𝕜 : Type*} [Field 𝕜]
    {V : Type*} [AddCommGroup V] [Module 𝕜 V] {Γ : Type} [Group Γ]
    (σ : Representation 𝕜 Γ V) {z : Γ} {K₀ : Subgroup Γ}
    (hKle : K₀ ≤ Subgroup.centralizer ({z} : Set Γ)) :
    ∃ ρ₀ : Representation 𝕜 ↥K₀ ↥(LinearMap.ker (σ z - 1)),
      ∀ (g : ↥K₀) (w : ↥(LinearMap.ker (σ z - 1))),
        ((ρ₀ g w : ↥(LinearMap.ker (σ z - 1))) : V) = σ (g : Γ) (w : V) := by
  have hWinv : ∀ g ∈ K₀, ∀ w ∈ LinearMap.ker (σ z - 1),
      σ g w ∈ LinearMap.ker (σ z - 1) := by
    intro g hg w hw
    have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp (hKle hg)
    have hmul : σ z * σ g = σ g * σ z := by
      rw [← map_mul, ← map_mul, hgz]
    have hcomm : σ z (σ g w) = σ g (σ z w) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, hmul]
    have hw' : σ z w = w := by
      have h := hw
      change (σ z - 1) w = 0 at h
      rw [LinearMap.sub_apply, sub_eq_zero] at h
      simpa using h
    have hfix : σ z (σ g w) = σ g w := by rw [hcomm, hw']
    change (σ z - 1) (σ g w) = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    simpa using hfix
  refine ⟨{ toFun := fun g => LinearMap.restrict (σ (g : Γ)) (hWinv (g : Γ) g.2)
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · refine LinearMap.ext fun w => Subtype.ext ?_
    simp
  · intro a b
    refine LinearMap.ext fun w => Subtype.ext ?_
    simp
  · intro g w
    rfl

private theorem fixed_eq_zero_of_ker_le {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜] {p : ℕ} [CharP 𝕜 p]
    (hp : p.Prime) (hp5 : 5 ≤ p)
    {Γ : Type} [Group Γ] [Finite Γ]
    {K₀ : Subgroup Γ} (hK0perf : Group.IsPerfect ↥K₀)
    {T : Type} [Group T] (π : Γ →* T) (hπ : Function.Surjective (π.comp K₀.subtype))
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hker3 : Nat.Coprime (Nat.card ↥(π.comp K₀.subtype).ker) 3)
    (hkerS : Group.IsSolvable ↥(π.comp K₀.subtype).ker)
    {I : Subgroup Γ} (hIK : I ≤ K₀)
    (hIA5 : Nonempty (↥(I.map π) ≃* alternatingGroup (Fin 5)))
    {W : Type*} [AddCommGroup W] [Module 𝕜 W] [FiniteDimensional 𝕜 W]
    (hW3 : Module.finrank 𝕜 W ≤ 3) (ρ₀ : Representation 𝕜 ↥K₀ W)
    (hρ : ρ₀.ker ≤ (π.comp K₀.subtype).ker)
    {w : W} (hw : ∀ g ∈ I.subgroupOf K₀, ρ₀ g w = w) : w = 0 := by
  have hImap : (I.subgroupOf K₀).map (π.comp K₀.subtype) = I.map π := by
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hIK]
  have hJ : Nonempty (↥((I.subgroupOf K₀).map (π.comp K₀.subtype)) ≃*
      alternatingGroup (Fin 5)) := by
    rw [hImap]
    exact hIA5
  exact eq_zero_of_finrank_le_three hp hp5 hK0perf hW3 ρ₀ (π.comp K₀.subtype) hπ hT hker3
    hkerS hρ hJ hw

theorem apply_eq_self_of_noKlein {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜] {p : ℕ} [CharP 𝕜 p]
    (hp : p.Prime) (hp5 : 5 ≤ p)
    {Γ : Type} [Group Γ] [Finite Γ] (hperf : Group.IsPerfect Γ)
    (hno : ∀ s t : Γ, s ^ 2 = 1 → t ^ 2 = 1 → s ≠ 1 → t ≠ 1 → s * t = t * s → s = t)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (σ : Representation 𝕜 Γ V)
    (hr3 : ∀ t : Γ, t ^ 2 = 1 → t ≠ 1 → Module.finrank 𝕜 (LinearMap.ker (σ t - 1)) ≤ 3)
    {T : Type} [Group T] (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hker3 : Nat.Coprime (Nat.card π.ker) 3) (hkerS : Group.IsSolvable π.ker)
    {d : Γ} (hd3 : d ^ 3 = 1) (hdZ : π d ∈ Subgroup.center T)
    {I : Subgroup Γ} (hIperf : Group.IsPerfect I)
    (hIA5 : Nonempty (↥(I.map π) ≃* alternatingGroup (Fin 5)))
    (hI2 : IsPGroup 2 ↥(I ⊓ π.ker)) (hId : I ≤ Subgroup.centralizer ({d} : Set Γ))
    {v : V} (hv : ∀ g ∈ I, σ g v = v) : σ d v = v := by
  classical
  obtain ⟨z, O, K₀, hzI, hz2, hz1, hOn, hOle, hKsup, hK0perf, hKle, hdK, hIK⟩ :=
    exists_noKlein_data hperf hno π hker3 hkerS hd3 hIperf hIA5 hI2 hId
  haveI : Group.IsPerfect ↥K₀ := hK0perf
  have hπ₀ : Function.Surjective (π.comp K₀.subtype) :=
    surjective_comp_subtype hπ hOn hOle hKsup
  obtain ⟨hker3', hkerS'⟩ := ker_comp_subtype_data (K₀ := K₀) π hker3 hkerS
  obtain ⟨ρ₀, hρ₀⟩ := exists_restrict_representation σ hKle
  have hvW : v ∈ LinearMap.ker (σ z - 1) := by
    change (σ z - 1) v = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    simpa using hv z hzI
  have hd3' : (⟨d, hdK⟩ : ↥K₀) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hdZ' : (π.comp K₀.subtype) ⟨d, hdK⟩ ∈ Subgroup.center T := hdZ
  have hW3 : Module.finrank 𝕜 ↥(LinearMap.ker (σ z - 1)) ≤ 3 := hr3 z hz2 hz1
  rcases mem_or_le_ker_of_normal hK0perf (π.comp K₀.subtype) hπ₀ hT hker3' hd3' hdZ'
    (K := ρ₀.ker) (MonoidHom.normal_ker ρ₀) with hdker | hle
  · have hone : ρ₀ ⟨d, hdK⟩ = 1 := MonoidHom.mem_ker.mp hdker
    have hcoe := hρ₀ ⟨d, hdK⟩ ⟨v, hvW⟩
    rw [hone] at hcoe
    simpa using hcoe.symm
  · have hzero : (⟨v, hvW⟩ : ↥(LinearMap.ker (σ z - 1))) = 0 :=
      fixed_eq_zero_of_ker_le hp hp5 hK0perf (π := π) hπ₀ hT hker3' hkerS' hIK hIA5 hW3 ρ₀
        hle (fun g hg => by
          refine Subtype.ext ?_
          rw [hρ₀ g ⟨v, hvW⟩]
          exact hv (g : Γ) hg)
    have hv0 : v = 0 := congrArg (fun x : ↥(LinearMap.ker (σ z - 1)) => (x : V)) hzero
    rw [hv0, map_zero]

end CFSG.RankThree.PartTwo.Sec16.Kcd166

end
