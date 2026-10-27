module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupA6Order8
import CFSG.LocalAnalysis.WeakClosure81.CFAutAlmostSimple
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E2Pair
public import CFSG.LocalAnalysis.WeakClosure81.InFSqComponents

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (InFGroup CompFactorAutInF CFAutInFGroup)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {Q : Type} [Group Q] [Finite Q]

theorem orbitClosure_le_or_le_inf_centralizer
    (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥) {K T Y : Subgroup Q}
    (hK : CFSG.IsComponent K) (hT : IsPGroup 2 T)
    (hKT : orbitClosure K T ⊔ T = ⊤) (hY : Y.Normal) :
    orbitClosure K T ≤ Y ∨
      Y ≤ orbitClosure K T ⊓ Subgroup.centralizer (orbitClosure K T : Set Q) := by
  by_cases hex : ∃ t ∈ T, K.map (MulAut.conj t).toMonoidHom ≤ Y
  · obtain ⟨t, ht, htY⟩ := hex
    exact Or.inl (orbitClosure_le_of_mem_le hY htY)
  · push Not at hex
    have hcomm : ∀ t ∈ T, ⁅K.map (MulAut.conj t).toMonoidHom, Y⁆ = ⊥ := fun t ht =>
      (comm_subgroup_map_conj_of_isComponent hK hY t).resolve_left (hex t ht)
    have hFleCY : orbitClosure K T ≤ Subgroup.centralizer (Y : Set Q) :=
      orbitClosure_le fun t ht =>
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm t ht)
    have hYleCF : Y ≤ Subgroup.centralizer (orbitClosure K T : Set Q) := by
      rw [Subgroup.le_centralizer_iff]
      exact hFleCY
    refine Or.inr (le_inf ?_ hYleCF)
    exact hYleCF.trans (centralizer_orbitClosure_le hO2 hT hKT)

theorem mem_centralizer_of_comm_mem_center_of_quasisimple {K' : Subgroup Q}
    (hK' : CFSG.IsQuasisimple K') {x : Q} (hx : x ∈ Subgroup.normalizer (K' : Set Q))
    (h : ∀ k ∈ K', x * k * x⁻¹ * k⁻¹ ∈ Subgroup.centralizer (K' : Set Q)) :
    x ∈ Subgroup.centralizer (K' : Set Q) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact ((CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.commute_of_comm_central hK' hx
    (fun k hk z hz => (Subgroup.mem_centralizer_iff.mp (h k hk) z hz).symm)) k hk).symm

theorem orbitClosure_map {Q' : Type} [Group Q'] (π : Q →* Q') (K T : Subgroup Q) :
    (orbitClosure K T).map π = orbitClosure (K.map π) (T.map π) := by
  apply le_antisymm
  · refine Subgroup.map_le_iff_le_comap.mpr (orbitClosure_le fun t ht => ?_)
    refine Subgroup.map_le_iff_le_comap.mp ?_
    rw [CFSG.LieType.Steinberg.map_map_conj]
    exact map_conj_le_orbitClosure (K.map π) (Subgroup.mem_map_of_mem π ht)
  · refine orbitClosure_le fun u hu => ?_
    obtain ⟨t, ht, rfl⟩ := hu
    rw [← CFSG.LieType.Steinberg.map_map_conj]
    exact Subgroup.map_mono (map_conj_le_orbitClosure K ht)

theorem conj_pow_four_not_mem_centralizer {K : Subgroup Q} {x y : Q}
    (h : x ^ 4 ∉ Subgroup.centralizer (K : Set Q)) :
    (y * x * y⁻¹) ^ 4 ∉
      Subgroup.centralizer (K.map (MulAut.conj y).toMonoidHom : Set Q) := by
  intro hmem
  apply h
  rw [Subgroup.mem_centralizer_iff] at hmem ⊢
  intro k hk
  have hk' : y * k * y⁻¹ ∈ K.map (MulAut.conj y).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
  have h1 := hmem (y * k * y⁻¹) hk'
  have hconj4 : (y * x * y⁻¹) ^ 4 = y * x ^ 4 * y⁻¹ := by
    simpa using map_pow (MulAut.conj y).toMonoidHom x 4
  rw [hconj4] at h1
  have h2 : y * (k * x ^ 4) * y⁻¹ = y * (x ^ 4 * k) * y⁻¹ := by
    have e1 : y * (k * x ^ 4) * y⁻¹ = (y * k * y⁻¹) * (y * x ^ 4 * y⁻¹) := by group
    have e2 : y * (x ^ 4 * k) * y⁻¹ = (y * x ^ 4 * y⁻¹) * (y * k * y⁻¹) := by group
    rw [e1, e2, h1]
  exact mul_left_cancel (mul_right_cancel h2)

theorem cFAutInFGroup_one_of_component_A6 (h410 : W4Lem4_10) {K S : Subgroup Q}
    (hK : CFSG.IsComponent K) (hS2 : IsPGroup 2 S)
    (hKT : orbitClosure K S ⊔ S = ⊤)
    (hA6 : Nonempty (↥K ≃* alternatingGroup (Fin 6)))
    (h8 : ∃ s ∈ S, s ∈ Subgroup.normalizer (K : Set Q) ∧
      s ^ 4 ∉ Subgroup.centralizer (K : Set Q)) :
    CFAutInFGroup 1 Q S := by
  classical
  apply cFAutInFGroup_one_of_A6 h410 S hS2
  intro X hXn hXne hXmin hXnc L hL
  let F : Subgroup Q := orbitClosure K S
  have hFnorm : F.Normal := orbitClosure_normal hKT
  have hQF2 : IsPGroup 2 (Q ⧸ F) := by
    have : F.Normal := hFnorm
    have : (F.subgroupOf (⊤ : Subgroup Q)).Normal := hFnorm.subgroupOf ⊤
    have htop : IsPGroup 2 ((⊤ : Subgroup Q) ⧸ F.subgroupOf ⊤) :=
      CFSG.Quasithin.F112R.isPGroup_quotient_of_sup_eq (p := 2) (G := Q)
        (L := F) (Q := S) (K := ⊤) hS2 le_top
        (by rw [Subgroup.normalizer_eq_top_iff.mpr hFnorm]; exact le_top) hKT
    have he : (F.subgroupOf (⊤ : Subgroup Q)).map
        (Subgroup.topEquiv (G := Q)).toMonoidHom = F := by
      ext x
      simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact IsPGroup.of_equiv htop
      (QuotientGroup.congr (F.subgroupOf ⊤) F Subgroup.topEquiv he)
  have hLcomp : CFSG.IsComponent L := by
    have hsub : CFSG.Open.IsSubnormal L ⊤ :=
      CFSG.Open.IsSubnormal.trans hL.2.1
        (CFSG.Open.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal hXn))
    exact ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hL.2.2,
      CFSG.Quasithin.A3.subnormal_top_iff.mp hsub⟩
  have hLleF : L ≤ F := by
    by_contra hnot
    let π : Q →* Q ⧸ F := QuotientGroup.mk' F
    have hmapne : L.map π ≠ ⊥ := fun hbot =>
      hnot (by simpa [π, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff L).mp hbot)
    have : Nontrivial ↥(L.map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hmapne
    have hsol : Group.IsSolvable ↥(L.map π) :=
      @IsNilpotent.to_isSolvable _ _ (hQF2.to_subgroup (L.map π)).isNilpotent
    have hperf : Group.IsPerfect ↥(L.map π) := by
      have : Group.IsPerfect ↥L := hLcomp.1.1
      exact Group.IsPerfect.map π
    exact Group.IsPerfect.not_isSolvable ↥(L.map π) hsol
  have hconj : ∃ s ∈ S, L = K.map (MulAut.conj s).toMonoidHom := by
    by_contra hnot
    push Not at hnot
    have hcomm : ∀ s ∈ S, ⁅K.map (MulAut.conj s).toMonoidHom, L⁆ = ⊥ := by
      intro s hs
      rcases CFSG.LocalCores.distinct_components_commute (isComponent_map_conjAut hK s)
        hLcomp with h | h
      · exact absurd h.symm (hnot s hs)
      · exact h
    have hFleC : F ≤ Subgroup.centralizer (L : Set Q) :=
      orbitClosure_le fun s hs =>
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm s hs)
    have hLleCF : L ≤ Subgroup.centralizer (F : Set Q) := by
      rw [Subgroup.le_centralizer_iff]
      exact hFleC
    have hLcomm : IsMulCommutative ↥L :=
      ⟨⟨fun a b => Subtype.ext
        ((Subgroup.mem_centralizer_iff.mp (hLleCF a.2) (b : Q) (hLleF b.2)).symm)⟩⟩
    have : Group.IsPerfect ↥L := hLcomp.1.1
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hLcomp.1
    exact Group.IsPerfect.not_isMulCommutative L hLcomm
  obtain ⟨s, hs, hsL⟩ := hconj
  obtain ⟨eA⟩ := hA6
  have hshape : Nonempty (↥L ≃* alternatingGroup (Fin 6)) := by
    rw [hsL]
    exact ⟨(Subgroup.equivMapOfInjective K (MulAut.conj s).toMonoidHom
      (MulAut.conj s).injective).symm.trans eA⟩
  obtain ⟨t, ht, htN, ht4⟩ := h8
  refine ⟨hshape, s * t * s⁻¹, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨S.mul_mem (S.mul_mem hs ht) (S.inv_mem hs), ?_⟩
    have h1 : s * t * s⁻¹ ∈ (Subgroup.normalizer (K : Set Q)).map
        (MulAut.conj s).toMonoidHom :=
      ⟨t, htN, by simp [MulAut.conj_apply]⟩
    rw [Subgroup.map_equiv_normalizer_eq] at h1
    rwa [← hsL] at h1
  · intro hmem
    exact conj_pow_four_not_mem_centralizer ht4 (hsL ▸ hmem)

theorem isComponent_map_of_inf_eq_center {Q' : Type} [Group Q'] (π : Q →* Q')
    (hπ : Function.Surjective π) {K Z : Subgroup Q} (hK : CFSG.IsComponent K)
    (hker : π.ker = Z) (hKZ : K ⊓ Z = (Subgroup.center ↥K).map K.subtype) :
    CFSG.IsComponent (K.map π) ∧
      Nonempty (↥(K.map π) ≃* ↥K ⧸ Subgroup.center ↥K) := by
  classical
  have hKnotle : ¬ K ≤ Z := by
    intro hle
    have h2 : K ≤ (Subgroup.center ↥K).map K.subtype := by
      rw [← hKZ, inf_eq_left.mpr hle]
    have hcent : ∀ a : ↥K, a ∈ Subgroup.center ↥K := fun a => by
      obtain ⟨z, hz, hza⟩ := Subgroup.mem_map.mp (h2 a.2)
      rw [show z = a from Subtype.ext hza] at hz
      exact hz
    have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
    have : Group.IsPerfect ↥K := hK.1.1
    refine Group.IsPerfect.not_isMulCommutative ↥K ⟨⟨fun a b => ?_⟩⟩
    exact (Subgroup.mem_center_iff.mp (hcent a) b).symm
  have hKnotleπ : ¬ K ≤ π.ker := by rw [hker]; exact hKnotle
  have hquasi : CFSG.IsQuasisimple (K.map π) :=
    CFSG.LocalCores.isQuasisimple_map hK.1 π hKnotleπ
  have hsub : (K.map π).IsSubnormal := Subgroup.IsSubnormal.map (f := π) hπ hK.2
  let f : ↥K →* ↥(K.map π) :=
    (π.comp K.subtype).codRestrict _ (fun x => Subgroup.mem_map.mpr ⟨(x : Q), x.2, rfl⟩)
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hfker : f.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hx1 : π (x : Q) = 1 := congrArg Subtype.val hx
      have hxZ : (x : Q) ∈ Z := by
        rw [← hker, MonoidHom.mem_ker]
        exact hx1
      have hxKZ : (x : Q) ∈ K ⊓ Z := ⟨x.2, hxZ⟩
      rw [hKZ] at hxKZ
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxKZ
      rw [show z = x from Subtype.ext hzx] at hz
      exact hz
    · intro hx
      have hxKZ : (x : Q) ∈ K ⊓ Z := by
        rw [hKZ]
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      exact Subtype.ext (by
        have hxZ : (x : Q) ∈ Z := hxKZ.2
        rw [← hker, MonoidHom.mem_ker] at hxZ
        exact hxZ)
  let e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(K.map π) :=
    (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfsurj)
  exact ⟨⟨hquasi, hsub⟩, ⟨e.symm⟩⟩

theorem pow_four_not_mem_centralizer_map {Q' : Type} [Group Q'] (π : Q →* Q')
    {K Z : Subgroup Q} (hK : CFSG.IsQuasisimple K)
    (hZ : Z ≤ Subgroup.centralizer (K : Set Q)) (hker : π.ker = Z) {x : Q}
    (hx : x ∈ Subgroup.normalizer (K : Set Q))
    (hx4 : x ^ 4 ∉ Subgroup.centralizer (K : Set Q)) :
    π x ^ 4 ∉ Subgroup.centralizer (K.map π : Set Q') := by
  intro hmem
  apply hx4
  have hx4N : x ^ 4 ∈ Subgroup.normalizer (K : Set Q) := Subgroup.pow_mem _ hx 4
  refine mem_centralizer_of_comm_mem_center_of_quasisimple hK hx4N ?_
  intro k hk
  refine hZ ?_
  rw [← hker, MonoidHom.mem_ker]
  have h1 := Subgroup.mem_centralizer_iff.mp hmem (π k) (Subgroup.mem_map_of_mem π hk)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_pow]
  calc (π x) ^ 4 * π k * ((π x) ^ 4)⁻¹ * (π k)⁻¹
      = (π k * (π x) ^ 4) * ((π x) ^ 4)⁻¹ * (π k)⁻¹ := by rw [h1]
    _ = 1 := by group

theorem compFactorAutInF_one_of_orbitClosure_A6 (h410 : W4Lem4_10)
    (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥) {K T : Subgroup Q} (hK : CFSG.IsComponent K)
    (hT : IsSylowIn 2 T ⊤) (hKT : orbitClosure K T ⊔ T = ⊤)
    (hA6 : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6)))
    (h8 : ∃ t ∈ T, t ∈ Subgroup.normalizer (K : Set Q) ∧
      t ^ 4 ∉ Subgroup.centralizer (K : Set Q)) :
    ∀ T' : Subgroup Q, CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ → CompFactorAutInF 1 ⊤ T' := by
  classical
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hFnorm : (orbitClosure K T).Normal := orbitClosure_normal hKT
  have hQF2 : IsPGroup 2 (Q ⧸ orbitClosure K T) := by
    have : (orbitClosure K T).Normal := hFnorm
    have : ((orbitClosure K T).subgroupOf (⊤ : Subgroup Q)).Normal :=
      hFnorm.subgroupOf ⊤
    have htop : IsPGroup 2 ((⊤ : Subgroup Q) ⧸ (orbitClosure K T).subgroupOf ⊤) :=
      CFSG.Quasithin.F112R.isPGroup_quotient_of_sup_eq (p := 2) (G := Q)
        (L := orbitClosure K T) (Q := T) (K := ⊤) hT2 le_top
        (by rw [Subgroup.normalizer_eq_top_iff.mpr hFnorm]; exact le_top) hKT
    have he : ((orbitClosure K T).subgroupOf (⊤ : Subgroup Q)).map
        (Subgroup.topEquiv (G := Q)).toMonoidHom = orbitClosure K T := by
      ext x
      simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact IsPGroup.of_equiv htop
      (QuotientGroup.congr ((orbitClosure K T).subgroupOf ⊤) (orbitClosure K T)
        Subgroup.topEquiv he)
  intro T' hT'
  have hT'in : IsSylowIn 2 T' ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT'
  obtain ⟨q, -, hq⟩ := CFSG.Quasithin.Ch1Sec3.exists_conj_of_isSylowIn hT hT'in
  have hT'eq : T' = T.map (MulAut.conj q).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨q⁻¹ * x * q, (hq x).mp hx, by simp [MulAut.conj_apply]; group⟩
    · rintro ⟨y, hy, rfl⟩
      exact (hq (q * y * q⁻¹)).mpr (by
        rw [show q⁻¹ * (q * y * q⁻¹) * q = y from by group]
        exact hy)
  set K' : Subgroup Q := K.map (MulAut.conj q).toMonoidHom with hK'def
  have hK' : CFSG.IsComponent K' := isComponent_map_conjAut hK q
  have hFconj : orbitClosure K' T' = orbitClosure K T := by
    rw [hK'def, hT'eq]
    exact (orbitClosure_map (MulAut.conj q).toMonoidHom K T).symm.trans
      (Subgroup.Normal.map_conj_eq (orbitClosure K T) q)
  have hFT' : orbitClosure K T ⊔ T' = ⊤ := by
    have : (orbitClosure K T).Normal := hFnorm
    let P : Sylow 2 Q := hT'in.isPGroup.toSylow (by simpa using hT'in.not_dvd_relIndex)
    have h := CFSG.section10_sylow_sup_normal_of_p_quotient_eq_top
      (N := orbitClosure K T) hQF2 P
    rw [IsPGroup.toSylow_coe] at h
    rw [sup_comm]
    exact h
  obtain ⟨t, ht, htN, ht4⟩ := h8
  have ht' : q * t * q⁻¹ ∈ T' := by
    rw [hT'eq]
    exact Subgroup.mem_map.mpr ⟨t, ht, by simp [MulAut.conj_apply]⟩
  have ht'N : q * t * q⁻¹ ∈ Subgroup.normalizer (K' : Set Q) := by
    have h1 : q * t * q⁻¹ ∈ (Subgroup.normalizer (K : Set Q)).map
        (MulAut.conj q).toMonoidHom := ⟨t, htN, by simp [MulAut.conj_apply]⟩
    rwa [Subgroup.map_equiv_normalizer_eq, ← hK'def] at h1
  have ht'4 : (q * t * q⁻¹) ^ 4 ∉ Subgroup.centralizer (K' : Set Q) :=
    conj_pow_four_not_mem_centralizer (K := K) (x := t) (y := q) ht4
  intro Y hY hYn
  have hYnorm : Y.Normal := by
    have h := (Subgroup.normal_subgroupOf_iff_le_normalizer (le_top : Y ≤ ⊤)).mp hYn
    exact Subgroup.normalizer_eq_top_iff.mp (le_antisymm le_top h)
  let NQ := ↥(⊤ : Subgroup Q) ⧸ Y.subgroupOf ⊤
  let π : Q →* NQ :=
    (QuotientGroup.mk' (Y.subgroupOf ⊤)).comp (Subgroup.topEquiv (G := Q)).symm.toMonoidHom
  have hπsurj : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (Subgroup.topEquiv (G := Q)).symm.surjective
  have hπker : π.ker = Y := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hx' : (Subgroup.topEquiv (G := Q)).symm x ∈ Y.subgroupOf ⊤ :=
        (QuotientGroup.eq_one_iff _).mp hx
      simpa [Subgroup.mem_subgroupOf] using hx'
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mpr (by
        simpa [Subgroup.mem_subgroupOf] using hx)
  by_cases hFY : orbitClosure K T ≤ Y
  · have hN2 : IsPGroup 2 NQ := by
      have hFYker : orbitClosure K T ≤ π.ker := by rw [hπker]; exact hFY
      refine IsPGroup.of_surjective hQF2
        (QuotientGroup.lift (orbitClosure K T) π hFYker) ?_
      exact QuotientGroup.lift_surjective_of_surjective _ π hπsurj hFYker
    exact cfAutInFGroup_of_isPGroup Nat.prime_two hN2 1 _
  · have hYleZ : Y ≤ orbitClosure K T ⊓
        Subgroup.centralizer (orbitClosure K T : Set Q) :=
      (orbitClosure_le_or_le_inf_centralizer hO2 hK hT2 hKT hYnorm).resolve_left hFY
    by_cases hZY : orbitClosure K T ⊓
        Subgroup.centralizer (orbitClosure K T : Set Q) ≤ Y
    · have hYZ : Y = orbitClosure K T ⊓
          Subgroup.centralizer (orbitClosure K T : Set Q) := le_antisymm hYleZ hZY
      have hZeq : (orbitClosure K T ⊓ Subgroup.centralizer (orbitClosure K T : Set Q)) =
          (Subgroup.center ↥(CFSG.layer Q)).map (CFSG.layer Q).subtype := by
        have hFeq : orbitClosure K T = CFSG.layer Q :=
          le_antisymm (orbitClosure_le_layer hK) (layer_le_orbitClosure hO2 hT2 hKT)
        rw [hFeq]
        ext x
        rw [Subgroup.mem_inf, CFSG.LocalCores.mem_map_center_iff]
      have hK'Z : K' ⊓ Y = (Subgroup.center ↥K').map K'.subtype := by
        rw [hYZ, hZeq]
        exact (CFSG.LocalCores.layer_center (G := Q)).2 K' hK'
      have hK'leF : K' ≤ orbitClosure K T := by
        rw [hK'def]
        calc K.map (MulAut.conj q).toMonoidHom ≤
              (orbitClosure K T).map (MulAut.conj q).toMonoidHom :=
              Subgroup.map_mono (le_orbitClosure K T)
          _ = orbitClosure K T := Subgroup.Normal.map_conj_eq (orbitClosure K T) q
      have hZcent : Y ≤ Subgroup.centralizer (K' : Set Q) := by
        rw [hYZ]
        exact inf_le_right.trans (Subgroup.centralizer_le hK'leF)
      obtain ⟨hKbar, ⟨eKbar⟩⟩ :=
        isComponent_map_of_inf_eq_center π hπsurj hK' hπker hK'Z
      have hA6bar : Nonempty (↥(K'.map π) ≃* alternatingGroup (Fin 6)) := by
        obtain ⟨eA⟩ := hA6
        have hquot : Nonempty ((↥K' ⧸ Subgroup.center ↥K') ≃*
            alternatingGroup (Fin 6)) := by
          let eKK' : ↥K' ≃* ↥K :=
            (Subgroup.equivMapOfInjective K (MulAut.conj q).toMonoidHom
              (MulAut.conj q).injective).symm
          exact ⟨(QuotientGroup.congr (Subgroup.center ↥K') (Subgroup.center ↥K) eKK'
            (Subgroup.map_center_eq eKK')).trans eA⟩
        exact ⟨eKbar.trans hquot.some⟩
      have hS2bar : IsPGroup 2 (T'.map π) := IsPGroup.map hT'in.isPGroup π
      have hKTbar : orbitClosure (K'.map π) (T'.map π) ⊔ T'.map π = ⊤ := by
        have h1 : orbitClosure (K'.map π) (T'.map π) = (orbitClosure K' T').map π :=
          (orbitClosure_map π K' T').symm
        rw [h1, hFconj, ← Subgroup.map_sup, hFT',
          Subgroup.map_top_of_surjective π hπsurj]
      have h8bar : ∃ s ∈ T'.map π, s ∈ Subgroup.normalizer ((K'.map π) : Set NQ) ∧
          s ^ 4 ∉ Subgroup.centralizer (K'.map π : Set NQ) := by
        refine ⟨π (q * t * q⁻¹), Subgroup.mem_map.mpr ⟨_, ht', rfl⟩, ?_, ?_⟩
        · exact Subgroup.le_normalizer_map (H := K') π (Subgroup.mem_map_of_mem π ht'N)
        · exact pow_four_not_mem_centralizer_map π hK'.1 hZcent hπker ht'N ht'4
      have hres := cFAutInFGroup_one_of_component_A6 h410 hKbar hS2bar hKTbar hA6bar h8bar
      have hSbarEq : T'.map π =
          (T'.subgroupOf ⊤).map (QuotientGroup.mk' (Y.subgroupOf ⊤)) := by
        rw [show π = (QuotientGroup.mk' (Y.subgroupOf ⊤)).comp
          (Subgroup.topEquiv (G := Q)).symm.toMonoidHom from rfl, ← Subgroup.map_map]
        congr 1
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          simpa [Subgroup.mem_subgroupOf] using hy
        · intro hx
          exact ⟨(x : Q), hx, Subtype.ext rfl⟩
      rwa [hSbarEq] at hres
    · intro X hXn hXne hXmin hXnc L hL
      exfalso
      have hXtil_norm : (X.comap π).Normal := hXn.comap π
      have hXtil_ne : X.comap π ≠ ⊥ := by
        intro hbot
        apply hXne
        have hmap : (X.comap π).map π = X :=
          Subgroup.map_comap_eq_self_of_surjective hπsurj X
        rw [hbot, Subgroup.map_bot] at hmap
        exact hmap.symm
      have hZcomm : IsMulCommutative ↥(orbitClosure K T ⊓
          Subgroup.centralizer (orbitClosure K T : Set Q)) := by
        refine ⟨⟨fun a b => ?_⟩⟩
        exact Subtype.ext
          (Subgroup.mem_centralizer_iff.mp a.2.2 (b : Q) b.2.1).symm
      have hZmap_comm : IsMulCommutative ↥((orbitClosure K T ⊓
          Subgroup.centralizer (orbitClosure K T : Set Q)).map π) := by
        refine ⟨⟨fun a b => ?_⟩⟩
        obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
        obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
        have h := congrArg (fun z : ↥(orbitClosure K T ⊓
            Subgroup.centralizer (orbitClosure K T : Set Q)) => π (z : Q))
          (hZcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
        apply Subtype.ext
        show (a : NQ) * (b : NQ) = (b : NQ) * (a : NQ)
        rw [← hxa, ← hyb]
        simpa using h
      rcases orbitClosure_le_or_le_inf_centralizer hO2 hK hT2 hKT hXtil_norm with
        hFX | hXZ
      · have hZle : orbitClosure K T ⊓
            Subgroup.centralizer (orbitClosure K T : Set Q) ≤ X.comap π :=
          inf_le_left.trans hFX
        have hZmap_le : (orbitClosure K T ⊓
            Subgroup.centralizer (orbitClosure K T : Set Q)).map π ≤ X := by
          rw [← Subgroup.map_comap_eq_self_of_surjective hπsurj X]
          exact Subgroup.map_mono hZle
        have hZmap_ne : (orbitClosure K T ⊓
            Subgroup.centralizer (orbitClosure K T : Set Q)).map π ≠ ⊥ := by
          intro hbot
          apply hZY
          intro z hz
          have hzπ : π z ∈ (orbitClosure K T ⊓
              Subgroup.centralizer (orbitClosure K T : Set Q)).map π :=
            Subgroup.mem_map_of_mem π hz
          rw [hbot] at hzπ
          rw [← hπker, MonoidHom.mem_ker]
          exact Subgroup.mem_bot.mp hzπ
        have hZmap_norm : ((orbitClosure K T ⊓
            Subgroup.centralizer (orbitClosure K T : Set Q)).map π).Normal := by
          have : (orbitClosure K T).Normal := hFnorm
          exact (Subgroup.normal_inf_normal _ _).map π hπsurj
        rcases hXmin _ hZmap_norm hZmap_le with hbot | htop
        · exact hZmap_ne hbot
        · exact hXnc (htop ▸ hZmap_comm)
      · have hXle : X ≤ (orbitClosure K T ⊓
            Subgroup.centralizer (orbitClosure K T : Set Q)).map π := by
          rw [← Subgroup.map_comap_eq_self_of_surjective hπsurj X]
          exact Subgroup.map_mono hXZ
        refine hXnc ⟨⟨fun a b => ?_⟩⟩
        have hcomm := congrArg Subtype.val (hZmap_comm.is_comm.comm
          ⟨a, hXle a.2⟩ ⟨b, hXle b.2⟩)
        exact Subtype.ext (by simpa using hcomm)

end CFSG.LocalAnalysis.WeakClosure81
