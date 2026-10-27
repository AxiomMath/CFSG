module

public import CFSG.GroupTheory.CoprimeCentralizerCover
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofA6
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open CFSG CFSG.RankThree.PartTwo
open CFSG.RankThreeCoreUniqueness.Helpers

theorem eq_inf_centralizer_sup_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {P H N : Subgroup G} (hP : IsPGroup p P) (hN : ¬ p ∣ Nat.card N)
    (hNH : N ≤ H) (hPH : P ≤ Subgroup.normalizer (H : Set G))
    (hPHN : ∀ x ∈ P, ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ ∈ N) :
    H = (H ⊓ Subgroup.centralizer (P : Set G)) ⊔ N := by
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h1 := hPHN x hx y (hNH hy)
      have h2 : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
      rw [h2]
      exact N.mul_mem h1 hy
    · intro hy
      have hx' : x⁻¹ ∈ P := P.inv_mem hx
      have h1 := hPHN x⁻¹ hx' (x * y * x⁻¹) (hNH hy)
      have h2 : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ * (x * y * x⁻¹)⁻¹ =
          y * (x * y * x⁻¹)⁻¹ := by group
      rw [h2] at h1
      have h3 : y = (y * (x * y * x⁻¹)⁻¹) * (x * y * x⁻¹) := by group
      rw [h3]
      exact N.mul_mem h1 hy
  have hcomm : ⁅H, P⁆ ≤ N := by
    have hcomm' : ⁅P, H⁆ ≤ N :=
      Subgroup.commutator_le.mpr fun x hx y hy => by
        simpa [commutatorElement_def] using hPHN x hx y hy
    rwa [Subgroup.commutator_comm]
  have h := CFSG.GroupTheory.inf_centralizer_sup_eq_of_commutator_le
    (p := p) (X := H) (N := N) (R := P) hNH hPH hPN hP hN hcomm
  exact h.symm

theorem eq_bot_of_quotient_mulEquiv_alternatingGroup_five {T : Type*} [Group T] [Finite T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) {K : Subgroup T} {N : Subgroup K}
    [N.Normal] (hN : IsPGroup 2 N) (hKN : Nonempty (K ⧸ N ≃* alternatingGroup (Fin 5))) :
    N = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hZcard, ⟨e6⟩⟩ := hT
  let σ : T →* alternatingGroup (Fin 6) :=
    e6.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center T))
  have hσker : σ.ker = Subgroup.center T := by
    ext x
    rw [MonoidHom.mem_ker]
    change e6 (QuotientGroup.mk x) = 1 ↔ x ∈ Subgroup.center T
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hZK_le_N : (Subgroup.center T).subgroupOf K ≤ N := by
    let πK : K →* K ⧸ N := QuotientGroup.mk' N
    have hZcenter : (Subgroup.center T).subgroupOf K ≤ Subgroup.center K := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro k
      have hzT : (z : T) ∈ Subgroup.center T := hz
      exact Subtype.ext ((Subgroup.mem_center_iff.mp hzT) (k : T))
    have hmap : ((Subgroup.center T).subgroupOf K).map πK ≤
        Subgroup.center (K ⧸ N) :=
      (Subgroup.map_mono hZcenter).trans
        (Subgroup.map_center_le_center (f := πK) (QuotientGroup.mk'_surjective N))
    have hcenter : Subgroup.center (K ⧸ N) = ⊥ := by
      obtain ⟨e5⟩ := hKN
      have h5 : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
        alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
      have hmaps : Subgroup.map e5.toMonoidHom (Subgroup.center (K ⧸ N)) = ⊥ := by
        have h := Subgroup.map_center_eq e5
        rw [h5] at h
        simpa using h
      exact (Subgroup.map_eq_bot_iff_of_injective
        (H := Subgroup.center (K ⧸ N)) (f := e5.toMonoidHom) e5.injective).mp hmaps
    have hmapbot : ((Subgroup.center T).subgroupOf K).map πK = ⊥ :=
      le_bot_iff.mp (hmap.trans (le_of_eq hcenter))
    have hle := (Subgroup.map_eq_bot_iff (f := πK) _).mp hmapbot
    simpa [πK, QuotientGroup.ker_mk'] using hle
  have hZbot : (Subgroup.center T).subgroupOf K = ⊥ := by
    have hZmap : ((Subgroup.center T).subgroupOf K).map K.subtype ≤
        Subgroup.center T := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
      exact hz
    have hZ3 : Nat.card ((Subgroup.center T).subgroupOf K) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le hZmap
      rwa [Subgroup.card_map_of_injective K.subtype_injective, hZcard] at h
    have hZN : Nat.card ((Subgroup.center T).subgroupOf K) ∣ Nat.card N :=
      Subgroup.card_dvd_of_le hZK_le_N
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN
    have hZ2 : Nat.card ((Subgroup.center T).subgroupOf K) ∣ 2 ^ k := by
      rwa [hk] at hZN
    rcases (Nat.dvd_prime Nat.prime_three).mp hZ3 with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have h23 : 3 ∣ 2 ^ k := h3 ▸ hZ2
      have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h23
      norm_num at h32
  have hσK : Function.Injective (σ.comp K.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff (σ.comp K.subtype)).mp
    rw [← MonoidHom.comap_ker, hσker, Subgroup.comap_subtype, hZbot]
  have hcardKmap : Nat.card (K.map σ) = Nat.card K := by
    have hrange : (σ.comp K.subtype).range = K.map σ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange]
    exact Nat.card_range_of_injective hσK
  have hqcard : Nat.card (K ⧸ N) = 60 := by
    obtain ⟨e5⟩ := hKN
    rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hcardK : Nat.card K = 60 * Nat.card N := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hqcard] at h
    exact h
  have hKmapdvd : Nat.card (K.map σ) ∣ 360 := by
    have hdvd := Subgroup.card_dvd_of_le (H := K.map σ) (K := ⊤) le_top
    rw [Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin] at hdvd
    norm_num at hdvd
    simpa [Nat.card_eq_fintype_card] using hdvd
  have hNdvd6 : Nat.card N ∣ 6 := by
    have hdiv : 60 * Nat.card N ∣ 360 := by
      rw [← hcardK, ← hcardKmap]
      exact hKmapdvd
    have h : 60 * Nat.card N ∣ 60 * 6 := by
      simpa using hdiv
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 60) h
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN
  have hk_le : k ≤ 2 := by
    by_contra h
    push Not at h
    have h8 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have h36 : 2 ^ 3 ∣ 6 := h8.trans (hk ▸ hNdvd6)
    norm_num at h36
  have hNcases : Nat.card N = 1 ∨ Nat.card N = 2 := by
    interval_cases k
    · left; exact hk.trans (by norm_num)
    · right; exact hk.trans (by norm_num)
    · exfalso
      have h46 : 2 ^ 2 ∣ 6 := by
        rw [← hk]
        exact hNdvd6
      norm_num at h46
  rcases hNcases with h1 | h2
  · exact Subgroup.eq_bot_of_card_eq N h1
  · exfalso
    have hcardKmap120 : Nat.card (K.map σ) = 120 := by
      rw [hcardKmap, hcardK, h2]
    have hidx : (K.map σ).index = 3 := by
      have hmul := Subgroup.card_mul_index (K.map σ)
      rw [hcardKmap120, nat_card_alternatingGroup, Nat.card_fin] at hmul
      norm_num at hmul
      omega
    have htop : K.map σ = ⊤ :=
      CFSG.RankThree.PartTwo.Sec14.Desc143X.A6.eq_top_of_index_le_five
        (MulEquiv.refl (alternatingGroup (Fin 6))) (by omega : (K.map σ).index ≤ 5)
    rw [htop, Subgroup.index_top] at hidx
    omega

private theorem finite_of_isTripleCover {T : Type*} [Group T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) : Finite T := by
  have hZfin : Finite (Subgroup.center T) :=
    Nat.finite_of_card_ne_zero (by rw [hT.1]; norm_num)
  have hQfin : Finite (T ⧸ Subgroup.center T) :=
    Finite.of_equiv (alternatingGroup (Fin 6)) hT.2.some.symm.toEquiv
  haveI : Finite ↥(Subgroup.center T) := hZfin
  haveI : Finite (T ⧸ Subgroup.center T) := hQfin
  exact Finite.of_subgroup_quotient (Subgroup.center T)

private theorem isPerfect_inSubgroup_perfectResidual {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) :
    Group.IsPerfect ↥(CFSG.inSubgroup CFSG.perfectResidual H) := by
  have h := (CFSG.perfect_residual_characterization (G := H)).2.2.1
  haveI : Group.IsPerfect (CFSG.perfectResidual H) := h
  exact Group.IsPerfect.map H.subtype

private def restrictMap {Γ T : Type*} [Group Γ] [Group T] (π : Γ →* T)
    (H : Subgroup Γ) : ↥H →* ↥(H.map π) :=
  (π.comp H.subtype).codRestrict _ (fun x => Subgroup.mem_map_of_mem π x.2)

private theorem restrictMap_surjective {Γ T : Type*} [Group Γ] [Group T]
    (π : Γ →* T) (H : Subgroup Γ) : Function.Surjective (restrictMap π H) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨x, hx⟩, rfl⟩

private theorem restrictMap_ker {Γ T : Type*} [Group Γ] [Group T]
    (π : Γ →* T) (H : Subgroup Γ) :
    (restrictMap π H).ker = (H ⊓ π.ker).subgroupOf H := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hx1 : π (x : Γ) = 1 := congrArg Subtype.val hx
    show (x : Γ) ∈ H ⊓ π.ker
    exact ⟨x.2, MonoidHom.mem_ker.mp hx1⟩
  · intro hx
    apply Subtype.ext
    have hx' : (x : Γ) ∈ H ⊓ π.ker := hx
    exact MonoidHom.mem_ker.mp hx'.2

private theorem perfectResidual_surjects_to_perfect_image {G Image : Type*} [Group G]
    [Finite G] [Group Image] [Group.IsPerfect Image] (f : G →* Image)
    (hf : Function.Surjective f) : (CFSG.perfectResidual G).map f = ⊤ := by
  have h := finite_perfectResidual_surjects_to_perfect_image f hf
  rwa [show CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual G =
    CFSG.perfectResidual G from rfl] at h

private theorem map_inSubgroup_perfectResidual_eq_of_perfect_map
    {Γ T : Type*} [Group Γ] [Finite Γ] [Group T] [Finite T]
    (π : Γ →* T) {H : Subgroup Γ}
    (hperf : Group.IsPerfect ↥(H.map π)) :
    (CFSG.inSubgroup CFSG.perfectResidual H).map π = H.map π := by
  haveI : Group.IsPerfect ↥(H.map π) := hperf
  let g := restrictMap π H
  have hcomp : (H.map π).subtype.comp g = π.comp H.subtype := by
    ext x
    rfl
  have hsurj := perfectResidual_surjects_to_perfect_image g
    (restrictMap_surjective π H)
  have h1 : (CFSG.perfectResidual ↥H).map (π.comp H.subtype) = H.map π := by
    calc (CFSG.perfectResidual ↥H).map (π.comp H.subtype)
        = ((CFSG.perfectResidual ↥H).map g).map (H.map π).subtype := by
            rw [← hcomp, ← Subgroup.map_map]
        _ = (⊤ : Subgroup ↥(H.map π)).map (H.map π).subtype := by rw [hsurj]
        _ = H.map π := by rw [Subgroup.map_top, Subgroup.range_subtype]
  calc (CFSG.inSubgroup CFSG.perfectResidual H).map π =
        ((CFSG.perfectResidual ↥H).map H.subtype).map π := rfl
    _ = (CFSG.perfectResidual ↥H).map (π.comp H.subtype) := by rw [Subgroup.map_map]
    _ = H.map π := h1

private theorem isSolvable_subgroupOf_inf_ker {Γ T : Type*} [Group Γ] [Group T]
    (π : Γ →* T) (hkerS : Group.IsSolvable π.ker) (I : Subgroup Γ) :
    Group.IsSolvable ↥((I ⊓ π.ker).subgroupOf I) := by
  let Nsub : Subgroup ↥I := (I ⊓ π.ker).subgroupOf I
  change Group.IsSolvable ↥Nsub
  have hNsub_eq : Nsub = (π.ker).subgroupOf I := by
    ext x
    show (x : Γ) ∈ I ⊓ π.ker ↔ (x : Γ) ∈ π.ker
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  rw [hNsub_eq]
  let f : ↥((π.ker).subgroupOf I) →* ↥(π.ker) :=
    { toFun := fun x => ⟨(x.1 : Γ), x.2⟩
      map_one' := by ext; rfl
      map_mul' := fun x y => by ext; rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(π.ker) => (z : Γ)) hxy
  haveI : Group.IsSolvable ↥(π.ker) := hkerS
  exact Group.isSolvable_of_isSolvable_injective (f := f) hf

private theorem subgroupOf_inf_ker_le_pCore {Γ T : Type*} [Group Γ] [Finite Γ] [Group T]
    (π : Γ →* T) (hkerS : Group.IsSolvable π.ker) {I : Subgroup Γ}
    (hIA5 : Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* alternatingGroup (Fin 5))) :
    (I ⊓ π.ker).subgroupOf I ≤ CFSG.pCore 2 ↥I := by
  classical
  let O : Subgroup ↥I := CFSG.pCore 2 ↥I
  let Nsub : Subgroup ↥I := (I ⊓ π.ker).subgroupOf I
  have hNnormal : Nsub.Normal := by
    rw [show Nsub = (restrictMap π I).ker from (restrictMap_ker π I).symm]
    exact MonoidHom.normal_ker _
  have hNsolv : Group.IsSolvable ↥Nsub := isSolvable_subgroupOf_inf_ker π hkerS I
  haveI : Group.IsSolvable ↥Nsub := hNsolv
  let q : ↥I →* ↥I ⧸ O := QuotientGroup.mk' O
  have hQnormal : (Nsub.map q).Normal :=
    hNnormal.map q (QuotientGroup.mk'_surjective O)
  have hQsolv : Group.IsSolvable ↥(Nsub.map q) := by
    let qN : ↥Nsub →* ↥(Nsub.map q) :=
      (q.comp Nsub.subtype).codRestrict _ (fun x => Subgroup.mem_map_of_mem q x.2)
    have hqN : Function.Surjective qN := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxq⟩
    exact Group.isSolvable_of_surjective (f := qN) hqN
  obtain ⟨e5⟩ := hIA5
  have hQne : Nsub.map q ≠ ⊤ := by
    intro htop
    have hqsurj : Function.Surjective (q.comp Nsub.subtype) := by
      intro y
      have hy : y ∈ Nsub.map q := by rw [htop]; exact Subgroup.mem_top y
      obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, hxq⟩
    have hsurj : Function.Surjective (e5.toMonoidHom.comp (q.comp Nsub.subtype)) :=
      e5.surjective.comp hqsurj
    have hsolv : Group.IsSolvable (alternatingGroup (Fin 5)) :=
      Group.isSolvable_of_surjective
        (f := e5.toMonoidHom.comp (q.comp Nsub.subtype)) hsurj
    haveI : Nontrivial (alternatingGroup (Fin 5)) :=
      alternatingGroup.nontrivial_of_three_le_card (by simp)
    haveI : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
    exact (Group.IsPerfect.not_isSolvable (G := alternatingGroup (Fin 5))) hsolv
  have hQbot : Nsub.map q = ⊥ := by
    haveI : IsSimpleGroup (↥I ⧸ O) := e5.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Nsub.map q) with h | h
    · exact h
    · exact absurd h hQne
  have hle : Nsub ≤ q.ker := (Subgroup.map_eq_bot_iff (f := q) (H := Nsub)).mp hQbot
  change Nsub ≤ O
  simpa [q, QuotientGroup.ker_mk'] using hle

private theorem inf_ker_le_pCore_map {Γ T : Type*} [Group Γ] [Finite Γ] [Group T]
    (π : Γ →* T) (hkerS : Group.IsSolvable π.ker) {I : Subgroup Γ}
    (hIA5 : Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* alternatingGroup (Fin 5))) :
    I ⊓ π.ker ≤ (CFSG.pCore 2 ↥I).map I.subtype := by
  have hle := subgroupOf_inf_ker_le_pCore π hkerS hIA5
  intro x hx
  have hxI : x ∈ I := hx.1
  let xI : ↥I := ⟨x, hxI⟩
  have hxNsub : xI ∈ (I ⊓ π.ker).subgroupOf I := hx
  have hxO : xI ∈ CFSG.pCore 2 ↥I := hle hxNsub
  exact Subgroup.mem_map.mpr ⟨xI, hxO, rfl⟩

private theorem pCore_map_le_ker {Γ T : Type*} [Group Γ] [Finite Γ] [Group T] [Finite T]
    (π : Γ →* T) (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    {I : Subgroup Γ}
    (hIA5 : Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* alternatingGroup (Fin 5)))
    (hkerS : Group.IsSolvable π.ker) :
    (CFSG.pCore 2 ↥I).map I.subtype ≤ π.ker := by
  classical
  let O : Subgroup ↥I := CFSG.pCore 2 ↥I
  have hNsub_le_O : (I ⊓ π.ker).subgroupOf I ≤ O :=
    subgroupOf_inf_ker_le_pCore π hkerS hIA5
  have hNsub2 : IsPGroup 2 ↥((I ⊓ π.ker).subgroupOf I) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).to_le hNsub_le_O
  have hker2 : IsPGroup 2 (restrictMap π I).ker := by
    rw [restrictMap_ker]
    exact hNsub2
  have hOmap : O.map (restrictMap π I) = CFSG.pCore 2 ↥(I.map π) :=
    CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker (p := 2)
      (restrictMap π I) (restrictMap_surjective π I) hker2
  have hePI : Nonempty ((↥I ⧸ O) ≃*
      (↥(I.map π) ⧸ CFSG.pCore 2 ↥(I.map π))) :=
    CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker (p := 2)
      (restrictMap π I) (restrictMap_surjective π I) hker2
  have hKN' : Nonempty (↥(I.map π) ⧸ CFSG.pCore 2 ↥(I.map π) ≃*
      alternatingGroup (Fin 5)) := by
    obtain ⟨ePI⟩ := hePI
    obtain ⟨e5⟩ := hIA5
    exact ⟨ePI.symm.trans e5⟩
  have hpcore_bot : CFSG.pCore 2 ↥(I.map π) = ⊥ :=
    eq_bot_of_quotient_mulEquiv_alternatingGroup_five hT
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(I.map π))) hKN'
  have hcomp : (I.map π).subtype.comp (restrictMap π I) = π.comp I.subtype := by
    ext x
    rfl
  have hπOa : (O.map I.subtype).map π = ⊥ := by
    calc (O.map I.subtype).map π = O.map (π.comp I.subtype) := by
          rw [Subgroup.map_map]
      _ = O.map ((I.map π).subtype.comp (restrictMap π I)) := by rw [hcomp]
      _ = (O.map (restrictMap π I)).map (I.map π).subtype := by
          rw [Subgroup.map_map]
      _ = (CFSG.pCore 2 ↥(I.map π)).map (I.map π).subtype := by rw [hOmap]
      _ = ⊥ := by rw [hpcore_bot, Subgroup.map_bot]
  exact (Subgroup.map_eq_bot_iff (f := π) (H := O.map I.subtype)).mp hπOa

private theorem inf_ker_eq_pCore_map {Γ T : Type*} [Group Γ] [Finite Γ] [Group T]
    [Finite T] (π : Γ →* T) (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    {I : Subgroup Γ}
    (hIA5 : Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* alternatingGroup (Fin 5)))
    (hkerS : Group.IsSolvable π.ker) :
    I ⊓ π.ker = (CFSG.pCore 2 ↥I).map I.subtype := by
  refine le_antisymm (inf_ker_le_pCore_map π hkerS hIA5) ?_
  exact le_inf (Subgroup.map_subtype_le _) (pCore_map_le_ker π hT hIA5 hkerS)

private theorem quotient_pCore_equiv_map {Γ T : Type*} [Group Γ] [Finite Γ] [Group T]
    (π : Γ →* T) {I : Subgroup Γ}
    (hker : I ⊓ π.ker = (CFSG.pCore 2 ↥I).map I.subtype) :
    Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* ↥(I.map π)) := by
  let fI := restrictMap π I
  have hker_fI : fI.ker = (I ⊓ π.ker).subgroupOf I := restrictMap_ker π I
  have hNsub : (I ⊓ π.ker).subgroupOf I = CFSG.pCore 2 ↥I := by
    rw [hker]
    exact Subgroup.comap_map_eq_self_of_injective I.subtype_injective _
  have hkerO : fI.ker = CFSG.pCore 2 ↥I := by rw [hker_fI, hNsub]
  exact ⟨QuotientGroup.liftEquiv (CFSG.pCore 2 ↥I)
    (restrictMap_surjective π I) hkerO.symm⟩

private theorem isPerfect_map_of_quotient_pCore {Γ T : Type*} [Group Γ] [Finite Γ]
    [Group T] (π : Γ →* T) {I : Subgroup Γ}
    (hIA5 : Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* alternatingGroup (Fin 5)))
    (hker : I ⊓ π.ker = (CFSG.pCore 2 ↥I).map I.subtype) :
    Group.IsPerfect ↥(I.map π) := by
  haveI : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
  obtain ⟨eI⟩ := quotient_pCore_equiv_map π hker
  obtain ⟨e5⟩ := hIA5
  exact Group.IsPerfect.ofSurjective (f := (e5.symm.trans eI).toMonoidHom)
    (e5.symm.trans eI).surjective

private theorem map_eq_of_eq_sup_of_le_ker {Γ T : Type*} [Group Γ] [Group T]
    (π : Γ →* T) {H A N : Subgroup Γ} (hH : H = A ⊔ N) (hN : N ≤ π.ker) :
    A.map π = H.map π := by
  conv_rhs => rw [hH]
  rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff (f := π) (H := N)).mpr hN,
    sup_bot_eq]

private theorem isPGroup_two_inf_ker {Γ T : Type*} [Group Γ] [Finite Γ] [Group T]
    (π : Γ →* T) {I : Subgroup Γ}
    (hker : I ⊓ π.ker = (CFSG.pCore 2 ↥I).map I.subtype) :
    IsPGroup 2 ↥(I ⊓ π.ker) := by
  rw [hker]
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).map I.subtype

private theorem cover_I {Γ T : Type*} [Group Γ] [Finite Γ] [Group T]
    (π : Γ →* T) {p : ℕ} [Fact p.Prime] {U I : Subgroup Γ}
    (hp2 : p ≠ 2) (hUp : IsPGroup p U) (hUD : U ≤ π.ker)
    (hUI : U ≤ Subgroup.normalizer (I : Set Γ))
    (hN2 : IsPGroup 2 ↥(I ⊓ π.ker)) :
    I = (I ⊓ Subgroup.centralizer (U : Set Γ)) ⊔ (I ⊓ π.ker) := by
  have hNp : ¬ p ∣ Nat.card ↥(I ⊓ π.ker) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq ‹Fact p.Prime›.out Nat.prime_two).1
      (‹Fact p.Prime›.out.dvd_of_dvd_pow h))
  have hcomm : ∀ x ∈ U, ∀ y ∈ I, x * y * x⁻¹ * y⁻¹ ∈ I ⊓ π.ker := by
    intro x hx y hy
    constructor
    · have hxN : x ∈ Subgroup.normalizer (I : Set Γ) := hUI hx
      exact I.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN y).mp hy) (I.inv_mem hy)
    · have hxD : x ∈ π.ker := hUD hx
      have hconj : y * x⁻¹ * y⁻¹ ∈ π.ker :=
        π.normal_ker.conj_mem x⁻¹ (π.ker.inv_mem hxD) y
      have h1 : x * (y * x⁻¹ * y⁻¹) ∈ π.ker := π.ker.mul_mem hxD hconj
      have h2 : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [h2]
      exact h1
  exact eq_inf_centralizer_sup_of_isPGroup (p := p) (P := U) (H := I)
    (N := I ⊓ π.ker) hUp hNp inf_le_left hUI hcomm

private theorem cover_centralizer_singleton {Γ T : Type*} [Group Γ] [Finite Γ] [Group T]
    (π : Γ →* T) {d : Γ} (hd3 : d ^ 3 = 1) (hdZ : π d ∈ Subgroup.center T)
    {H : Subgroup Γ} (hdH : d ∈ Subgroup.normalizer (H : Set Γ))
    (hN2 : IsPGroup 2 ↥(H ⊓ π.ker)) :
    H = (H ⊓ Subgroup.centralizer ({d} : Set Γ)) ⊔ (H ⊓ π.ker) := by
  have hP2 : IsPGroup 3 (Subgroup.zpowers d) := by
    have hd3card : Nat.card (Subgroup.zpowers d) ∣ 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_iff_pow_eq_one.mpr hd3
    exact IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hd3card)
  have hNnot3 : ¬ 3 ∣ Nat.card ↥(H ⊓ π.ker) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
    intro h3
    have h3dvd : 3 ∣ 2 ^ k := by rwa [hk] at h3
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3dvd
    norm_num at h32
  have hP2H : Subgroup.zpowers d ≤ Subgroup.normalizer (H : Set Γ) :=
    Subgroup.zpowers_le.mpr hdH
  have hP2N : ∀ x ∈ Subgroup.zpowers d, ∀ y ∈ H,
      x * y * x⁻¹ * y⁻¹ ∈ H ⊓ π.ker := by
    intro x hx y hy
    constructor
    · have hxN : x ∈ Subgroup.normalizer (H : Set Γ) := hP2H hx
      exact H.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN y).mp hy) (H.inv_mem hy)
    · have hxπ : π x ∈ Subgroup.zpowers (π d) := by
        rw [← MonoidHom.map_zpowers π d]
        exact Subgroup.mem_map_of_mem π hx
      have hxcenter : π x ∈ Subgroup.center T := (Subgroup.zpowers_le.mpr hdZ) hxπ
      have hcomm : π y * π x = π x * π y :=
        (Subgroup.mem_center_iff.mp hxcenter) (π y)
      have hπ1 : π (x * y * x⁻¹ * y⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        rw [← hcomm]
        group
      exact MonoidHom.mem_ker.mpr hπ1
  have hcent_zp : Subgroup.centralizer (Subgroup.zpowers d : Set Γ) =
      Subgroup.centralizer ({d} : Set Γ) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have h := eq_inf_centralizer_sup_of_isPGroup (p := 3) (P := Subgroup.zpowers d)
    (H := H) (N := H ⊓ π.ker) hP2 hNnot3 inf_le_left hP2H hP2N
  simpa [hcent_zp] using h

private theorem exists_iOne_I0 {Γ T : Type*} [Group Γ] [Finite Γ] [Group T]
    (π : Γ →* T) (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hkerS : Group.IsSolvable π.ker)
    {d : Γ} {I : Subgroup Γ}
    (hIA5 : Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* alternatingGroup (Fin 5)))
    (hdI : d ∈ Subgroup.normalizer (I : Set Γ))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Subgroup Γ} (hUp : IsPGroup p U)
    (hUD : U ≤ π.ker) (hUI : U ≤ Subgroup.normalizer (I : Set Γ))
    (hdU : d ∈ Subgroup.normalizer (U : Set Γ)) :
    ∃ I₀ : Subgroup Γ, I₀ ≤ I ∧ Group.IsPerfect ↥I₀ ∧
      I₀ ≤ Subgroup.centralizer (U : Set Γ) ∧
      d ∈ Subgroup.normalizer (I₀ : Set Γ) ∧
      I₀.map π = I.map π ∧ IsPGroup 2 ↥(I₀ ⊓ π.ker) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite T := finite_of_isTripleCover hT
  let O : Subgroup ↥I := CFSG.pCore 2 ↥I
  have hker_eq : I ⊓ π.ker = O.map I.subtype :=
    inf_ker_eq_pCore_map π hT hIA5 hkerS
  have hN2 : IsPGroup 2 ↥(I ⊓ π.ker) := isPGroup_two_inf_ker π hker_eq
  set C : Subgroup Γ := I ⊓ Subgroup.centralizer (U : Set Γ) with hC
  have hcover1 : I = C ⊔ (I ⊓ π.ker) := cover_I π hp2 hUp hUD hUI hN2
  have hCmap : C.map π = I.map π :=
    map_eq_of_eq_sup_of_le_ker π hcover1 inf_le_right
  have hperfI : Group.IsPerfect ↥(I.map π) :=
    isPerfect_map_of_quotient_pCore π hIA5 hker_eq
  have hCperf : Group.IsPerfect ↥(C.map π) := by rw [hCmap]; exact hperfI
  let I₀ : Subgroup Γ := CFSG.inSubgroup CFSG.perfectResidual C
  have hI₀mapC : I₀.map π = C.map π :=
    map_inSubgroup_perfectResidual_eq_of_perfect_map π hCperf
  have hI₀map : I₀.map π = I.map π := hI₀mapC.trans hCmap
  have hI₀perf : Group.IsPerfect ↥I₀ := isPerfect_inSubgroup_perfectResidual C
  have hI₀leC : I₀ ≤ C := Subgroup.map_subtype_le _
  have hI₀leI : I₀ ≤ I := hI₀leC.trans inf_le_left
  have hI₀CU : I₀ ≤ Subgroup.centralizer (U : Set Γ) := hI₀leC.trans inf_le_right
  have hdC : d ∈ Subgroup.normalizer (C : Set Γ) := by
    have hdCU : d ∈ Subgroup.normalizer
        (Subgroup.centralizer (U : Set Γ) : Set Γ) :=
      (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer U) hdU
    exact (Subgroup.inf_normalizer_le_normalizer_inf (H := I)
      (K := Subgroup.centralizer (U : Set Γ))) ⟨hdI, hdCU⟩
  have hdI₀ : d ∈ Subgroup.normalizer (I₀ : Set Γ) := by
    have h := normalizer_le_normalizer_characteristic_map (G := Γ) C
      (CFSG.perfectResidual C) (inferInstance : (CFSG.perfectResidual C).Characteristic)
    simpa [I₀, CFSG.inSubgroup] using h hdC
  have hI₀N2 : IsPGroup 2 ↥(I₀ ⊓ π.ker) :=
    hN2.to_le (inf_le_inf_right π.ker hI₀leI)
  exact ⟨I₀, hI₀leI, hI₀perf, hI₀CU, hdI₀, hI₀map, hI₀N2⟩

private theorem exists_iOne_from_I0 {Γ T : Type*} [Group Γ] [Finite Γ] [Group T]
    [Finite T] (π : Γ →* T) {d : Γ} (hd3 : d ^ 3 = 1)
    (hdZ : π d ∈ Subgroup.center T) {I : Subgroup Γ}
    (hker_eq : I ⊓ π.ker = (CFSG.pCore 2 ↥I).map I.subtype)
    (hIA5 : Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* alternatingGroup (Fin 5)))
    (hperfI : Group.IsPerfect ↥(I.map π))
    {U : Subgroup Γ} {I₀ : Subgroup Γ}
    (hI₀leI : I₀ ≤ I) (hI₀perf : Group.IsPerfect ↥I₀)
    (hI₀CU : I₀ ≤ Subgroup.centralizer (U : Set Γ))
    (hdI₀ : d ∈ Subgroup.normalizer (I₀ : Set Γ))
    (hI₀map : I₀.map π = I.map π) (hI₀N2 : IsPGroup 2 ↥(I₀ ⊓ π.ker)) :
    ∃ I₁ : Subgroup Γ, I₁ ≤ I ∧ Group.IsPerfect ↥I₁ ∧
      I₁ ≤ Subgroup.centralizer ({d} : Set Γ) ∧ I₁ ≤ Subgroup.centralizer (U : Set Γ) ∧
      IsPGroup 2 ↥(I₁ ⊓ π.ker) ∧ Nonempty (↥(I₁.map π) ≃* alternatingGroup (Fin 5)) := by
  classical
  set C₁ : Subgroup Γ := I₀ ⊓ Subgroup.centralizer ({d} : Set Γ) with hC₁
  have hcover2 : I₀ = C₁ ⊔ (I₀ ⊓ π.ker) :=
    cover_centralizer_singleton π hd3 hdZ hdI₀ hI₀N2
  have hC₁map : C₁.map π = I₀.map π :=
    map_eq_of_eq_sup_of_le_ker π hcover2 inf_le_right
  have hC₁perf : Group.IsPerfect ↥(C₁.map π) := by
    rw [hC₁map, hI₀map]
    exact hperfI
  let I₁ : Subgroup Γ := CFSG.inSubgroup CFSG.perfectResidual C₁
  have hI₁mapC : I₁.map π = C₁.map π :=
    map_inSubgroup_perfectResidual_eq_of_perfect_map π hC₁perf
  have hI₁map : I₁.map π = I.map π := hI₁mapC.trans (hC₁map.trans hI₀map)
  have hI₁perf : Group.IsPerfect ↥I₁ := isPerfect_inSubgroup_perfectResidual C₁
  have hI₁leC₁ : I₁ ≤ C₁ := Subgroup.map_subtype_le _
  have hI₁leI₀ : I₁ ≤ I₀ := hI₁leC₁.trans inf_le_left
  have hI₁leI : I₁ ≤ I := hI₁leI₀.trans hI₀leI
  have hI₁Cd : I₁ ≤ Subgroup.centralizer ({d} : Set Γ) :=
    hI₁leC₁.trans inf_le_right
  have hI₁CU : I₁ ≤ Subgroup.centralizer (U : Set Γ) := hI₁leI₀.trans hI₀CU
  have hI₁N2 : IsPGroup 2 ↥(I₁ ⊓ π.ker) :=
    hI₀N2.to_le (inf_le_inf_right π.ker hI₁leI₀)
  obtain ⟨eI⟩ := quotient_pCore_equiv_map π hker_eq
  obtain ⟨e5⟩ := hIA5
  have hI₁iso : Nonempty (↥(I₁.map π) ≃* alternatingGroup (Fin 5)) := by
    rw [hI₁map]
    exact ⟨eI.symm.trans e5⟩
  exact ⟨I₁, hI₁leI, hI₁perf, hI₁Cd, hI₁CU, hI₁N2, hI₁iso⟩

private theorem exists_iOne_core {Γ T : Type*} [Group Γ] [Finite Γ] [Group T]
    (π : Γ →* T) (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hkerS : Group.IsSolvable π.ker)
    {d : Γ} (hd3 : d ^ 3 = 1) (hdZ : π d ∈ Subgroup.center T)
    {I : Subgroup Γ} (hIA5 : Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* alternatingGroup (Fin 5)))
    (hdI : d ∈ Subgroup.normalizer (I : Set Γ))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Subgroup Γ} (hUp : IsPGroup p U)
    (hUD : U ≤ π.ker) (hUI : U ≤ Subgroup.normalizer (I : Set Γ))
    (hdU : d ∈ Subgroup.normalizer (U : Set Γ)) :
    ∃ I₁ : Subgroup Γ, I₁ ≤ I ∧ Group.IsPerfect ↥I₁ ∧
      I₁ ≤ Subgroup.centralizer ({d} : Set Γ) ∧ I₁ ≤ Subgroup.centralizer (U : Set Γ) ∧
      IsPGroup 2 ↥(I₁ ⊓ π.ker) ∧ Nonempty (↥(I₁.map π) ≃* alternatingGroup (Fin 5)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite T := finite_of_isTripleCover hT
  have hker_eq : I ⊓ π.ker = (CFSG.pCore 2 ↥I).map I.subtype :=
    inf_ker_eq_pCore_map π hT hIA5 hkerS
  have hperfI : Group.IsPerfect ↥(I.map π) :=
    isPerfect_map_of_quotient_pCore π hIA5 hker_eq
  obtain ⟨I₀, hI₀leI, hI₀perf, hI₀CU, hdI₀, hI₀map, hI₀N2⟩ :=
    exists_iOne_I0 π hT hkerS hIA5 hdI hp hp2 hUp hUD hUI hdU
  exact exists_iOne_from_I0 π hd3 hdZ hker_eq hIA5 hperfI
    hI₀leI hI₀perf hI₀CU hdI₀ hI₀map hI₀N2

theorem exists_iOne {Γ T : Type*} [Group Γ] [Finite Γ] [Group T] (π : Γ →* T)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hkerS : Group.IsSolvable π.ker)
    {d : Γ} (hd3 : d ^ 3 = 1) (hdZ : π d ∈ Subgroup.center T)
    {I : Subgroup Γ} (hIA5 : Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* alternatingGroup (Fin 5)))
    (hdI : d ∈ Subgroup.normalizer (I : Set Γ))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Subgroup Γ} (hUp : IsPGroup p U)
    (hUD : U ≤ π.ker) (hUI : U ≤ Subgroup.normalizer (I : Set Γ))
    (hdU : d ∈ Subgroup.normalizer (U : Set Γ)) :
    ∃ I₁ : Subgroup Γ, I₁ ≤ I ∧ Group.IsPerfect ↥I₁ ∧
      I₁ ≤ Subgroup.centralizer ({d} : Set Γ) ∧ I₁ ≤ Subgroup.centralizer (U : Set Γ) ∧
      IsPGroup 2 ↥(I₁ ⊓ π.ker) ∧ Nonempty (↥(I₁.map π) ≃* alternatingGroup (Fin 5)) :=
  exists_iOne_core π hT hkerS hd3 hdZ hIA5 hdI hp hp2 hUp hUD hUI hdU

end CFSG.RankThree.PartTwo.Sec16.Kcd166
