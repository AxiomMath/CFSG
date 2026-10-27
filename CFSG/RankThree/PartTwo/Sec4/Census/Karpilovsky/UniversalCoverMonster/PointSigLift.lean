module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSigTransfer
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSigSignalizers
import CFSG.RankThree.PartTwo.Sec14.Item148ONLocProofSig
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.GroupTheory
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {A L R : Subgroup Γ} {b : Γ} (d : Data A L R b)

omit d in
theorem Data.le_normalizer_L (d : Data A L R b) : L ⊔ R ≤ Subgroup.normalizer (L : Set Γ) :=
  sup_le Subgroup.le_normalizer d.normL_R

theorem bar_inf_L_normal {W : Subgroup Γ} (hW : W ≤ L ⊔ R) :
    bar d W ≤ Subgroup.normalizer (↑(bar d (W ⊓ L)) : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :=
  bar_le_normalizer_bar d fun _ hw =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hw, Data.le_normalizer_L d (hW hw)⟩

theorem le_bar_inf_L {W : Subgroup Γ} (hW : W ≤ L ⊔ R)
    {T : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)} (hT : T ∈ thetaComponentsIn (bar d W))
    (h3 : 3 ∣ Nat.card T) : T ≤ bar d (W ⊓ L) := by
  obtain ⟨hTW, hT'⟩ := mem_thetaComponentsIn_iff.mp hT
  set T' := T.subgroupOf (bar d W) with hT'def
  have hJW : bar d (W ⊓ L) ≤ bar d W := bar_mono d inf_le_left
  have hnormJ : ((bar d (W ⊓ L)).subgroupOf (bar d W)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJW).mpr (bar_inf_L_normal d hW)
  set N' : Subgroup ↥T' := ((bar d (W ⊓ L)).subgroupOf (bar d W)).subgroupOf T' with hN'def
  have h3' : 3 ∣ Nat.card T' := by
    rwa [hT'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTW).toEquiv]
  have htop : N' = ⊤ := by
    refine eq_top_of_pow_three_mem hT'.1 hT'.2.2 h3' N' ?_
    intro x k hk
    have hx : ((x : ↥(bar d W)) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) ∈ bar d W := (x : ↥(bar d W)).2
    have hk' : ((x : ↥(bar d W)) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) ^ 3 ^ k = 1 := by
      have := congrArg (fun y : ↥T' => ((y : ↥(bar d W)) : ↥L ⧸ aschbacherSolvableCore 3 ↥L)) hk
      simpa using this
    exact mem_bar_inf_L_of_pow_three d hx hk'
  intro t ht
  have : (⟨⟨t, hTW ht⟩, ht⟩ : ↥T') ∈ N' := htop ▸ Subgroup.mem_top _
  exact this

omit d in
theorem isSolvable_thL_sub (L : Subgroup Γ) : Group.IsSolvable ↥(thL L) := by
  have : Group.IsSolvable ↥(aschbacherSolvableCore 3 ↥L) := isSolvable_thL L
  exact Group.isSolvable_of_surjective
    (f := ((aschbacherSolvableCore 3 ↥L).equivMapOfInjective L.subtype L.subtype_injective).toMonoidHom)
    ((aschbacherSolvableCore 3 ↥L).equivMapOfInjective L.subtype L.subtype_injective).surjective

theorem exists_lift_component {W : Subgroup Γ} (hW : W ≤ L ⊔ R)
    (hAW : A ≤ Subgroup.normalizer (W : Set Γ))
    {T : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)} (hT : T ∈ thetaComponentsIn (bar d W))
    (hPT : bar d A ≤ Subgroup.normalizer (↑T : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    (h3 : 3 ∣ Nat.card T) :
    ∃ K : Subgroup Γ, K ∈ thetaComponentsIn W ∧ K ≤ L ∧
      A ≤ Subgroup.normalizer (K : Set Γ) ∧ bar d K = T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hTW, hT'⟩ := mem_thetaComponentsIn_iff.mp hT
  have hTJ := le_bar_inf_L d hW hT h3
  let ρW : ↥W →* ↥(bar d W) :=
    ((rho d).comp (Subgroup.inclusion hW)).codRestrict (bar d W)
      fun w => rho_mem_bar d (hW w.2) w.2
  have hρW : ∀ w : ↥W, ((ρW w : ↥(bar d W)) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) =
      rho d ⟨w, hW w.2⟩ := fun w => rfl
  set T' : Subgroup ↥(bar d W) := T.subgroupOf (bar d W) with hT'def
  set J' : Subgroup ↥W := L.subgroupOf W with hJ'def
  set Jh : Subgroup ↥W := J' ⊓ T'.comap ρW with hJh
  set K' : Subgroup ↥W := inSubgroup perfectResidual Jh with hK'
  have hJhimg : Jh.map ρW = T' := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hw.2
    · intro t ht
      obtain ⟨g, hg, ⟨hgW, hgL⟩, hgt⟩ := (mem_bar d).mp (hTJ ht)
      refine ⟨⟨g, hgW⟩, ⟨hgL, ?_⟩, ?_⟩
      · show ρW ⟨g, hgW⟩ ∈ T'
        have : ((ρW ⟨g, hgW⟩ : ↥(bar d W)) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) = t := by
          rw [hρW]
          exact hgt
        show ((ρW ⟨g, hgW⟩ : ↥(bar d W)) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) ∈ T
        rw [this]
        exact ht
      · apply Subtype.ext
        rw [hρW]
        exact hgt
  have hK'img : K'.map ρW = T' := by
    set f : ↥Jh →* ↥(bar d W) := ρW.comp Jh.subtype with hf
    have hrange : f.range = T' := by
      rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, hJhimg]
    have h := (perfect_residual_transport f).1
    have hperfT' : Group.IsPerfect ↥(f.range) := hrange ▸ hT'.1
    rw [hK', inSubgroup, Subgroup.map_map]
    have : ρW.comp Jh.subtype = f := rfl
    rw [this, h, ← inSubgroup, inSubgroup_perfectResidual_of_isPerfect hperfT', hrange]
  have hKperf : Group.IsPerfect ↥K' := by
    obtain ⟨-, -, hperf, -⟩ := perfect_residual_characterization (G := ↥Jh)
    have := hperf
    exact Group.IsPerfect.map Jh.subtype
  have hK'Jh : K' ≤ Jh := Subgroup.map_subtype_le _
  have hJhL : ∀ w ∈ Jh, (w : Γ) ∈ L := fun w hw => hw.1
  have hJ'norm : J'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : Γ) ∈ L := hn
    have : ((g * n * g⁻¹ : ↥W) : Γ) ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Data.le_normalizer_L d (hW g.2)) n).mp hn'
      simpa using this
    exact this
  have hJhsn : Jh.IsSubnormal :=
    (Subgroup.Normal.isSubnormal hJ'norm).inf (Subgroup.IsSubnormal.comap ρW hT'.2.1)
  have hK'sn : K'.IsSubnormal := by
    refine Subgroup.IsSubnormal.trans hK'Jh ?_ hJhsn
    have hcomap : K'.subgroupOf Jh = perfectResidual ↥Jh := by
      rw [hK', inSubgroup, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
        Jh.subtype_injective]
    rw [hcomap]
    obtain ⟨-, hchar, -, -⟩ := perfect_residual_characterization (G := ↥Jh)
    exact Subgroup.Normal.isSubnormal inferInstance
  let φ : ↥K' →* ↥T' :=
    (ρW.comp K'.subtype).codRestrict T' fun k => (hK'Jh k.2).2
  have hφsurj : Function.Surjective φ := by
    intro t
    have : (t : ↥(bar d W)) ∈ K'.map ρW := by
      rw [hK'img]
      exact t.2
    obtain ⟨k, hk, hkt⟩ := this
    exact ⟨⟨k, hk⟩, Subtype.ext hkt⟩
  have hker : ∀ k : ↥φ.ker, ((k : ↥K') : ↥W).1 ∈ thL L := by
    intro k
    have h1 : φ k.1 = 1 := k.2
    have h2 : ρW (k.1 : ↥W) = 1 := by
      exact congrArg Subtype.val h1
    have hkL : (((k : ↥K') : ↥W) : Γ) ∈ L := hJhL _ (hK'Jh k.1.2)
    have h3 : rho d ⟨_, hW (k.1 : ↥W).2⟩ = 1 := by
      rw [← hρW]
      rw [h2]
      rfl
    rw [rho_mk_of_mem d _ hkL] at h3
    exact (mk_eq_one_iff L ⟨_, hkL⟩).mp h3
  let g : ↥φ.ker →* ↥(thL L) :=
    { toFun := fun k => ⟨((k : ↥K') : ↥W).1, hker k⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hginj : Function.Injective g := fun u v h => by
    have := congrArg (fun x : ↥(thL L) => (x : Γ)) h
    exact Subtype.ext (Subtype.ext (Subtype.ext this))
  have hsolker : Group.IsSolvable ↥φ.ker :=
    have := isSolvable_thL_sub L
    Group.isSolvable_of_isSolvable_injective hginj
  have h3ker : ¬ 3 ∣ Nat.card φ.ker := fun h =>
    card_thL_coprime L (h.trans (Subgroup.card_dvd_of_injective g hginj))
  obtain ⟨e⟩ := ONLoc.nonempty_thetaQuot_equiv φ hφsurj hsolker h3ker
  have hKq : IsQuasisimple (↥K' ⧸ aschbacherSolvableCore 3 ↥K') :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e hT'.2.2
  have hK'mem : K' ∈ thetaComponents 3 ↥W := ⟨hKperf, hK'sn, hKq⟩
  let φa : ∀ a : Γ, a ∈ A → MulAut ↥W := fun a ha => W.normalizerMonoidHom ⟨a, hAW ha⟩
  have hφa : ∀ (a : Γ) (ha : a ∈ A) (w : ↥W), ((φa a ha w : ↥W) : Γ) = a * w * a⁻¹ :=
    fun a ha w => rfl
  have hconjA : ∀ (a : Γ) (ha : a ∈ A), ∀ w ∈ Jh, φa a ha w ∈ Jh := by
    intro a ha w hw
    have haLR : a ∈ L ⊔ R := d.le_sup ha
    have hwLR : (w : Γ) ∈ L ⊔ R := hW w.2
    refine ⟨?_, ?_⟩
    · show ((φa a ha w : ↥W) : Γ) ∈ L
      rw [hφa a ha w]
      exact (Subgroup.mem_normalizer_iff.mp (d.normL ha) w).mp hw.1
    · show ρW (φa a ha w) ∈ T'
      show ((ρW (φa a ha w) : ↥(bar d W)) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) ∈ T
      have hmem' : ((φa a ha w : ↥W) : Γ) ∈ L ⊔ R := hW (φa a ha w).2
      have e : (⟨((φa a ha w : ↥W) : Γ), hmem'⟩ : ↥(L ⊔ R)) =
          ⟨a, haLR⟩ * ⟨(w : Γ), hwLR⟩ * ⟨a, haLR⟩⁻¹ := Subtype.ext (hφa a ha w)
      have h1 : ((ρW (φa a ha w) : ↥(bar d W)) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) =
          rho d ⟨a, haLR⟩ * rho d ⟨(w : Γ), hwLR⟩ * (rho d ⟨a, haLR⟩)⁻¹ := by
        rw [hρW, e, map_mul, map_mul, map_inv]
      rw [h1]
      have hra : rho d ⟨a, haLR⟩ ∈ bar d A := rho_mem_bar d haLR ha
      exact (Subgroup.mem_normalizer_iff.mp (hPT hra) _).mp hw.2
  have hJhmap : ∀ (a : Γ) (ha : a ∈ A), Jh.map (φa a ha).toMonoidHom = Jh := by
    intro a ha
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hconjA a ha w hw
    · intro w hw
      refine ⟨φa a⁻¹ (inv_mem ha) w, hconjA a⁻¹ (inv_mem ha) w hw, ?_⟩
      apply Subtype.ext
      show ((φa a ha (φa a⁻¹ (inv_mem ha) w) : ↥W) : Γ) = w
      rw [hφa a ha, hφa a⁻¹ (inv_mem ha) w]
      group
  have hK'map : ∀ (a : Γ) (ha : a ∈ A), K'.map (φa a ha).toMonoidHom = K' := by
    intro a ha
    rw [hK', map_inSubgroup_perfectResidual (φa a ha) Jh, hJhmap a ha]
  refine ⟨K'.map W.subtype, ⟨K', hK'mem, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact (hK'Jh hk).1
  · refine le_normalizer_of_conj_mem fun a ha x hx => ?_
    obtain ⟨k, hk, rfl⟩ := hx
    have : φa a ha k ∈ K' := by
      rw [← hK'map a ha]
      exact ⟨k, hk, rfl⟩
    refine ⟨φa a ha k, this, ?_⟩
    exact hφa a ha k
  · apply le_antisymm
    · intro x hx
      obtain ⟨g, hg, ⟨k, hk, rfl⟩, rfl⟩ := (mem_bar d).mp hx
      have : ρW k ∈ K'.map ρW := ⟨k, hk, rfl⟩
      rw [hK'img] at this
      exact this
    · intro t ht
      have : (⟨t, hTW ht⟩ : ↥(bar d W)) ∈ K'.map ρW := by
        rw [hK'img]
        exact ht
      obtain ⟨k, hk, hkt⟩ := this
      refine (mem_bar d).mpr ⟨(k : Γ), hW k.2, ⟨k, hk, rfl⟩, ?_⟩
      have := congrArg (fun y : ↥(bar d W) => (y : ↥L ⧸ aschbacherSolvableCore 3 ↥L)) hkt
      simpa [hρW] using this

omit [Finite Γ] d in
theorem conj_mem_signalizers {A K V : Subgroup Γ} {c : Γ} (hcK : c ∈ K)
    (hcA : c ∈ Subgroup.centralizer (A : Set Γ))
    (hV : V ≤ K ∧ V ∈ invariantPiSubgroups ⊤ A (piCompl 3) ∧ V = ⁅V, A⁆) :
    V.map (MulAut.conj c).toMonoidHom ≤ K ∧
      V.map (MulAut.conj c).toMonoidHom ∈ invariantPiSubgroups ⊤ A (piCompl 3) ∧
      V.map (MulAut.conj c).toMonoidHom = ⁅V.map (MulAut.conj c).toMonoidHom, A⁆ := by
  have hcomm : ∀ a ∈ A, a * c = c * a := fun a ha => Subgroup.mem_centralizer_iff.mp hcA a ha
  have hAmap : A.map (MulAut.conj c).toMonoidHom = A := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      have : c * a * c⁻¹ = a := by rw [← hcomm a ha]; group
      show c * a * c⁻¹ ∈ A
      rw [this]
      exact ha
    · intro a ha
      refine ⟨a, ha, ?_⟩
      show c * a * c⁻¹ = a
      rw [← hcomm a ha]
      group
  refine ⟨?_, ⟨le_top, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact K.mul_mem (K.mul_mem hcK (hV.1 hv)) (K.inv_mem hcK)
  · intro q hq
    refine hV.2.1.2.1 q ?_
    rwa [Subgroup.card_map_of_injective (MulAut.conj c).injective] at hq
  · refine le_normalizer_of_conj_mem fun a ha x hx => ?_
    obtain ⟨v, hv, rfl⟩ := hx
    have hV' : a * v * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hV.2.1.2.2 ha) v).mp hv
    refine ⟨a * v * a⁻¹, hV', ?_⟩
    show c * (a * v * a⁻¹) * c⁻¹ = a * (c * v * c⁻¹) * a⁻¹
    have h1 : c * a = a * c := (hcomm a ha).symm
    calc c * (a * v * a⁻¹) * c⁻¹ = (c * a) * v * (c * a)⁻¹ := by group
      _ = (a * c) * v * (a * c)⁻¹ := by rw [h1]
      _ = a * (c * v * c⁻¹) * a⁻¹ := by group
  · conv_lhs => rw [hV.2.2]
    rw [Subgroup.map_commutator, hAmap]

theorem exists_component_of_image {W : Subgroup Γ} (hW : W ≤ L ⊔ R)
    (hAW : A ≤ Subgroup.normalizer (W : Set Γ))
    {T : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)} (hT : T ∈ thetaComponentsIn (bar d W))
    (hPT : bar d A ≤ Subgroup.normalizer (↑T : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    (h3 : 3 ∣ Nat.card T)
    (hΔ : T ≤ sSup {V' : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) | V' ≤ T ∧
      V' ∈ invariantPiSubgroups ⊤ (bar d A) (piCompl 3) ∧ V' = ⁅V', bar d A⁆})
    (hsol : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (A : Set Γ))) :
    ∃ K ∈ thetaComponentsIn W, K ≤ L ∧
      K ≤ sSup {V : Subgroup Γ | V ≤ K ∧ V ∈ invariantPiSubgroups ⊤ A (piCompl 3) ∧
        V = ⁅V, A⁆} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hKmem, hKL, hAK, hbarK⟩ := exists_lift_component d hW hAW hT hPT h3
  refine ⟨K, hKmem, hKL, ?_⟩
  have hKperf : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hKmem
  have hKW : K ≤ W := le_of_mem_thetaComponentsIn hKmem
  have hKLR : K ≤ L ⊔ R := hKW.trans hW
  set S : Set (Subgroup Γ) := {V : Subgroup Γ | V ≤ K ∧ V ∈ invariantPiSubgroups ⊤ A (piCompl 3) ∧
    V = ⁅V, A⁆} with hS
  set J : Subgroup Γ := sSup S with hJ
  have hJK : J ≤ K := sSup_le fun V hV => hV.1
  have hJS : ∀ V ∈ S, V ≤ J := fun V hV => le_sSup hV
  have hAp := Data.isPGroup_A d
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (d.isE27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hTJ : T ≤ bar d J := by
    refine hΔ.trans (sSup_le fun V' hV' => ?_)
    have hbot : bar d (⊥ : Subgroup Γ) = ⊥ := by
      apply le_antisymm
      · intro x hx
        obtain ⟨g, hg, hg1, rfl⟩ := (mem_bar d).mp hx
        have : g = 1 := hg1
        subst this
        have h1 : rho d ⟨1, hg⟩ = 1 := by
          have : (⟨1, hg⟩ : ↥(L ⊔ R)) = 1 := rfl
          rw [this, map_one]
        rw [h1]
        exact Subgroup.one_mem _
      · exact bot_le
    have hC : V' ≤ Subgroup.centralizer (↑(bar d (⊥ : Subgroup Γ)) : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
      rw [hbot]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have : y = 1 := by simpa using hy
      rw [this]
      simp
    obtain ⟨V, hVle, hVinv, hVc, hV'V⟩ := exists_lift_signalizer d (W := K) (H := ⊥) hKLR
      bot_le hAK (hbarK ▸ hV'.1) hC hV'.2.1 hV'.2.2
    have hVK : V ≤ K := hVle.trans inf_le_left
    exact hV'V.trans (bar_mono d (hJS V ⟨hVK, hVinv, hVc⟩))
  set N : Subgroup Γ := K ⊓ thL L with hN
  have hNK : N ≤ K := inf_le_left
  have hAθ : A ≤ Subgroup.normalizer (thL L : Set Γ) :=
    d.normL.trans (normalizer_le_normalizer_thL L)
  have hAN : A ≤ Subgroup.normalizer (N : Set Γ) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hAK ha, hAθ ha⟩
  have hN3 : ¬ 3 ∣ Nat.card N := fun h =>
    card_thL_coprime L (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hKNJ : ∀ k ∈ K, ∃ n ∈ N, ∃ j ∈ J, k = n * j := by
    intro k hk
    have hkLR : k ∈ L ⊔ R := hKLR hk
    have hkT : rho d ⟨k, hkLR⟩ ∈ T := hbarK ▸ rho_mem_bar d hkLR hk
    obtain ⟨j, hjLR, hjJ, hjk⟩ := (mem_bar d).mp (hTJ hkT)
    have hkL : k ∈ L := hKL hk
    have hjL : j ∈ L := hKL (hJK hjJ)
    rw [rho_mk_of_mem d hjLR hjL, rho_mk_of_mem d hkLR hkL] at hjk
    refine ⟨k * j⁻¹, ⟨K.mul_mem hk (K.inv_mem (hJK hjJ)), ?_⟩, j, hjJ, by group⟩
    have : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) (⟨k * j⁻¹, L.mul_mem hkL (L.inv_mem hjL)⟩ : ↥L) = 1 := by
      have e : (⟨k * j⁻¹, L.mul_mem hkL (L.inv_mem hjL)⟩ : ↥L) = ⟨k, hkL⟩ * ⟨j, hjL⟩⁻¹ := rfl
      rw [e, map_mul, map_inv, ← hjk, mul_inv_cancel]
    exact (mk_eq_one_iff L _).mp this
  have hVN : ⁅N, A⁆ ≤ J := by
    refine hJS _ ⟨?_, ⟨le_top, ?_, ?_⟩, ?_⟩
    · exact (CFSG.LargeEvenClassification.Helpers.commutator_le_of_normalized N A hAN).trans hNK
    · intro q hq
      have hle : (⁅N, A⁆ : Subgroup Γ) ≤ N :=
        CFSG.LargeEvenClassification.Helpers.commutator_le_of_normalized N A hAN
      have hq3 : ¬ 3 ∣ Nat.card (⁅N, A⁆ : Subgroup Γ) := fun h =>
        hN3 (h.trans (Subgroup.card_dvd_of_le hle))
      show (q : ℕ) ≠ 3
      intro h
      exact hq3 (h ▸ hq)
    · exact Subgroup.normalizer_commutator_ge_right N A
    · exact (CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
        Nat.prime_three A N hAp hN3 hAN).symm
  set C : Subgroup Γ := K ⊓ Subgroup.centralizer (A : Set Γ) with hC
  have hCK : C ≤ K := inf_le_left
  have hKCJ : K ≤ C ⊔ J := by
    intro k hk
    obtain ⟨n, hnN, j, hjJ, rfl⟩ := hKNJ k hk
    obtain ⟨f, hf, t, ht, hft⟩ :=
      CFSG.LargeEvenClassification.Helpers.coprime_normalized_fixed_decomposition
        Nat.prime_three A N hAp hN3 hAN ⟨n, hnN⟩
    have hn : n = (f : Γ) * (t : Γ) := by rw [← Subgroup.coe_mul, hft]
    rw [hn, mul_assoc]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hNK f.2, hf⟩)
      (Subgroup.mem_sup_right (J.mul_mem (hVN ht) hjJ))
  have hCJ : C ≤ Subgroup.normalizer (J : Set Γ) := by
    refine le_normalizer_of_conj_mem fun c hc x hx => ?_
    have hle : J ≤ J.comap (MulAut.conj c).toMonoidHom := by
      refine sSup_le fun V hV => ?_
      obtain ⟨h1, h2, h3'⟩ := conj_mem_signalizers hc.1 hc.2 hV
      intro v hv
      exact hJS _ ⟨h1, h2, h3'⟩ ⟨v, hv, rfl⟩
    exact hle hx
  have hKN : K ≤ Subgroup.normalizer (J : Set Γ) :=
    hKCJ.trans (sup_le hCJ Subgroup.le_normalizer)
  have hsolC : Group.IsSolvable ↥C := by
    have : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (A : Set Γ)) := hsol
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_inf_right _ hKL : C ≤ L ⊓ Subgroup.centralizer (A : Set Γ)))
  exact le_of_perfect_of_le_sup_solvable hKperf hJK hCK hKN hKCJ hsolC

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig
