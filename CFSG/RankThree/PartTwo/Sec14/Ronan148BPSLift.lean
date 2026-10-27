module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSBar
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSigLift
import CFSG.RankThree.PartTwo.Sec14.Item148ONLocProofSig
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B.PS

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig (thL
  card_thL_coprime normalizer_le_normalizer_thL eq_top_of_pow_three_mem isSolvable_thL_sub
  le_normalizer_of_conj_mem conj_mem_signalizers le_of_perfect_of_le_sup_solvable)
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

namespace LRData

variable {L R : Subgroup Γ} (d : LRData L R)
include d

theorem mem_bar_inf_L_of_pow_three {W : Subgroup Γ} (hW : W ≤ L ⊔ R)
    {x : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)} (hx : x ∈ bar L W) {k : ℕ}
    (hk : x ^ 3 ^ k = 1) : x ∈ bar L (W ⊓ L) := by
  obtain ⟨w, hwN, hwW, rfl⟩ := mem_bar.mp hx
  have hwLR : w ∈ L ⊔ R := hW hwW
  have hu : w ^ 3 ^ k ∈ kerLR L R := by
    refine mem_kerLR.mpr ⟨⟨pow_mem hwN _, ?_⟩, pow_mem hwLR _⟩
    have : (⟨w ^ 3 ^ k, pow_mem hwN _⟩ : ↥(Subgroup.normalizer (L : Set Γ))) =
        (⟨w, hwN⟩ : ↥(Subgroup.normalizer (L : Set Γ))) ^ 3 ^ k := rfl
    rw [this, map_pow, hk]
  have hker3 : ¬ 3 ∣ Nat.card (kerLR L R) := d.not_dvd_card_of_le_kerLR le_rfl
  have hm : Nat.Coprime 3 (orderOf (w ^ 3 ^ k)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ hu)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hker3)
  set m := orderOf (w ^ 3 ^ k) with hmdef
  have hw'pow : (w ^ m) ^ 3 ^ k = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hmdef, pow_orderOf_eq_one]
  have hw'L : w ^ m ∈ L := d.mem_L_of_pow_three_pow (pow_mem hwLR m) hw'pow
  have hxm : phi L ⟨w ^ m, pow_mem hwN m⟩ ∈ bar L (W ⊓ L) :=
    phi_mem_bar (pow_mem hwN m) ⟨pow_mem hwW m, hw'L⟩
  have hxm' : phi L ⟨w ^ m, pow_mem hwN m⟩ = (phi L ⟨w, hwN⟩) ^ m := by
    rw [← map_pow]
    rfl
  rw [hxm'] at hxm
  have hord : orderOf (phi L ⟨w, hwN⟩) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime m (orderOf (phi L ⟨w, hwN⟩)) :=
    Nat.Coprime.coprime_dvd_right hord (Nat.Coprime.pow_right k (Nat.Coprime.symm hm))
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hn]
  exact pow_mem hxm n

theorem bar_inf_L_normal {W : Subgroup Γ} (hW : W ≤ L ⊔ R) :
    bar L W ≤ Subgroup.normalizer
      (↑(bar L (W ⊓ L)) : Set (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :=
  bar_le_normalizer_bar fun _ hw =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hw, d.sup_le_normalizer (hW hw)⟩

theorem le_bar_inf_L {W : Subgroup Γ} (hW : W ≤ L ⊔ R)
    {T : Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))} (hT : T ∈ thetaComponentsIn (bar L W))
    (h3 : 3 ∣ Nat.card T) : T ≤ bar L (W ⊓ L) := by
  obtain ⟨hTW, hT'⟩ := mem_thetaComponentsIn_iff.mp hT
  set T' := T.subgroupOf (bar L W) with hT'def
  have hJW : bar L (W ⊓ L) ≤ bar L W := bar_mono inf_le_left
  have hnormJ : ((bar L (W ⊓ L)).subgroupOf (bar L W)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJW).mpr (d.bar_inf_L_normal hW)
  set N' : Subgroup ↥T' := ((bar L (W ⊓ L)).subgroupOf (bar L W)).subgroupOf T' with hN'def
  have h3' : 3 ∣ Nat.card T' := by
    rwa [hT'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTW).toEquiv]
  have htop : N' = ⊤ := by
    refine eq_top_of_pow_three_mem hT'.1 hT'.2.2 h3' N' ?_
    intro x k hk
    have hx : ((x : ↥(bar L W)) : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ∈ bar L W :=
      (x : ↥(bar L W)).2
    have hk' : ((x : ↥(bar L W)) : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ^ 3 ^ k = 1 := by
      have := congrArg (fun y : ↥T' =>
        ((y : ↥(bar L W)) : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))) hk
      simpa using this
    exact d.mem_bar_inf_L_of_pow_three hW hx hk'
  intro t ht
  have : (⟨⟨t, hTW ht⟩, ht⟩ : ↥T') ∈ N' := htop ▸ Subgroup.mem_top _
  exact this

theorem exists_lift_component {A W : Subgroup Γ} (hAL : A ≤ Subgroup.normalizer (L : Set Γ))
    (hW : W ≤ L ⊔ R) (hAW : A ≤ Subgroup.normalizer (W : Set Γ))
    {T : Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))} (hT : T ∈ thetaComponentsIn (bar L W))
    (hPT : bar L A ≤ Subgroup.normalizer (↑T : Set (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))))
    (h3 : 3 ∣ Nat.card T) :
    ∃ K : Subgroup Γ, K ∈ thetaComponentsIn W ∧ K ≤ L ∧
      A ≤ Subgroup.normalizer (K : Set Γ) ∧ bar L K = T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hTW, hT'⟩ := mem_thetaComponentsIn_iff.mp hT
  have hTJ := d.le_bar_inf_L hW hT h3
  have hWN : W ≤ Subgroup.normalizer (L : Set Γ) := hW.trans d.sup_le_normalizer
  let ρW : ↥W →* ↥(bar L W) :=
    ((phi L).comp (Subgroup.inclusion hWN)).codRestrict (bar L W)
      fun w => phi_mem_bar (hWN w.2) w.2
  have hρW : ∀ w : ↥W, ((ρW w : ↥(bar L W)) : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) =
      phi L ⟨w, hWN w.2⟩ := fun w => rfl
  set T' : Subgroup ↥(bar L W) := T.subgroupOf (bar L W) with hT'def
  set J' : Subgroup ↥W := L.subgroupOf W with hJ'def
  set Jh : Subgroup ↥W := J' ⊓ T'.comap ρW with hJh
  set K' : Subgroup ↥W := inSubgroup perfectResidual Jh with hK'
  have hJhimg : Jh.map ρW = T' := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hw.2
    · intro t ht
      obtain ⟨g, hg, ⟨hgW, hgL⟩, hgt⟩ := mem_bar.mp (hTJ ht)
      refine ⟨⟨g, hgW⟩, ⟨hgL, ?_⟩, ?_⟩
      · show ((ρW ⟨g, hgW⟩ : ↥(bar L W)) : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ∈ T
        rw [hρW]
        exact hgt ▸ ht
      · apply Subtype.ext
        rw [hρW]
        exact hgt
  have hK'img : K'.map ρW = T' := by
    set f : ↥Jh →* ↥(bar L W) := ρW.comp Jh.subtype with hf
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
      have := (Subgroup.mem_normalizer_iff.mp (hWN g.2) n).mp hn'
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
    have : (t : ↥(bar L W)) ∈ K'.map ρW := by
      rw [hK'img]
      exact t.2
    obtain ⟨k, hk, hkt⟩ := this
    exact ⟨⟨k, hk⟩, Subtype.ext hkt⟩
  have hker : ∀ k : ↥φ.ker, ((k : ↥K') : ↥W).1 ∈ thL L := by
    intro k
    have h1 : φ k.1 = 1 := k.2
    have h2 : ρW (k.1 : ↥W) = 1 := congrArg Subtype.val h1
    have hkL : (((k : ↥K') : ↥W) : Γ) ∈ L := hJhL _ (hK'Jh k.1.2)
    have h3 : phi L ⟨_, hWN (k.1 : ↥W).2⟩ = 1 := by
      rw [← hρW, h2]
      rfl
    exact (d.phi_eq_one_iff hkL _).mp h3
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
    have haN := hAL ha
    have hwN : (w : Γ) ∈ Subgroup.normalizer (L : Set Γ) := hWN w.2
    refine ⟨?_, ?_⟩
    · show ((φa a ha w : ↥W) : Γ) ∈ L
      rw [hφa a ha w]
      exact (Subgroup.mem_normalizer_iff.mp haN w).mp hw.1
    · show ((ρW (φa a ha w) : ↥(bar L W)) : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ∈ T
      have e : (⟨((φa a ha w : ↥W) : Γ), hWN (φa a ha w).2⟩ :
          ↥(Subgroup.normalizer (L : Set Γ))) = ⟨a, haN⟩ * ⟨(w : Γ), hwN⟩ * ⟨a, haN⟩⁻¹ :=
        Subtype.ext (hφa a ha w)
      rw [hρW, e, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hPT (phi_mem_bar haN ha)) _).mp
        (show ((ρW w : ↥(bar L W)) : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ∈ T from hw.2)
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
    exact ⟨φa a ha k, this, hφa a ha k⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨g, hg, ⟨k, hk, rfl⟩, rfl⟩ := mem_bar.mp hx
      have : ρW k ∈ K'.map ρW := ⟨k, hk, rfl⟩
      rw [hK'img] at this
      exact this
    · intro t ht
      have : (⟨t, hTW ht⟩ : ↥(bar L W)) ∈ K'.map ρW := by
        rw [hK'img]
        exact ht
      obtain ⟨k, hk, hkt⟩ := this
      refine mem_bar.mpr ⟨(k : Γ), hWN k.2, ⟨k, hk, rfl⟩, ?_⟩
      have := congrArg (fun y : ↥(bar L W) => (y : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))) hkt
      simpa [hρW] using this

theorem exists_component_of_image {A W : Subgroup Γ} (hAp : IsPGroup 3 A)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAL : A ≤ Subgroup.normalizer (L : Set Γ))
    (hAR : A ≤ Subgroup.normalizer (R : Set Γ)) (hW : W ≤ L ⊔ R)
    (hAW : A ≤ Subgroup.normalizer (W : Set Γ))
    {T : Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))} (hT : T ∈ thetaComponentsIn (bar L W))
    (hPT : bar L A ≤ Subgroup.normalizer (↑T : Set (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))))
    (h3 : 3 ∣ Nat.card T)
    (hΔ : T ≤ sSup {V' : Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) | V' ≤ T ∧
      V' ∈ invariantPiSubgroups ⊤ (bar L A) (piCompl 3) ∧ V' = ⁅V', bar L A⁆}) :
    ∃ K ∈ thetaComponentsIn W, K ≤ L ∧
      K ≤ sSup {V : Subgroup Γ | V ≤ K ∧ V ∈ invariantPiSubgroups ⊤ A (piCompl 3) ∧
        V = ⁅V, A⁆} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hKmem, hKL, hAK, hbarK⟩ := d.exists_lift_component hAL hW hAW hT hPT h3
  refine ⟨K, hKmem, hKL, ?_⟩
  have hKperf : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hKmem
  have hKW : K ≤ W := le_of_mem_thetaComponentsIn hKmem
  have hKLR : K ≤ L ⊔ R := hKW.trans hW
  have hKN : K ≤ Subgroup.normalizer (L : Set Γ) := hKLR.trans d.sup_le_normalizer
  set S : Set (Subgroup Γ) := {V : Subgroup Γ | V ≤ K ∧ V ∈ invariantPiSubgroups ⊤ A (piCompl 3) ∧
    V = ⁅V, A⁆} with hS
  set J : Subgroup Γ := sSup S with hJ
  have hJK : J ≤ K := sSup_le fun V hV => hV.1
  have hJS : ∀ V ∈ S, V ≤ J := fun V hV => le_sSup hV
  have hTJ : T ≤ bar L J := by
    refine hΔ.trans (sSup_le fun V' hV' => ?_)
    have hC : V' ≤ Subgroup.centralizer
        (↑(bar L (⊥ : Subgroup Γ)) : Set (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))) := by
      rw [bar_bot]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have : y = 1 := by simpa using hy
      rw [this]
      simp
    obtain ⟨V, hVle, hVinv, hVc, hV'V⟩ := d.exists_lift_signalizer (W := K) (H := ⊥) hAp hAc hAL
      hAR hKLR bot_le hAK (hbarK ▸ hV'.1) hC hV'.2.1 hV'.2.2
    exact hV'V.trans (bar_mono (hJS V ⟨hVle.trans inf_le_left, hVinv, hVc⟩))
  set N : Subgroup Γ := K ⊓ thL L with hN
  have hNK : N ≤ K := inf_le_left
  have hAθ : A ≤ Subgroup.normalizer (thL L : Set Γ) := hAL.trans (normalizer_le_normalizer_thL L)
  have hAN : A ≤ Subgroup.normalizer (N : Set Γ) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hAK ha, hAθ ha⟩
  have hN3 : ¬ 3 ∣ Nat.card N := fun h =>
    card_thL_coprime L (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hKNJ : ∀ k ∈ K, ∃ n ∈ N, ∃ j ∈ J, k = n * j := by
    intro k hk
    have hkT : phi L ⟨k, hKN hk⟩ ∈ T := hbarK ▸ phi_mem_bar (hKN hk) hk
    obtain ⟨j, hjN, hjJ, hjk⟩ := mem_bar.mp (hTJ hkT)
    have hkL : k ∈ L := hKL hk
    have hjL : j ∈ L := hKL (hJK hjJ)
    refine ⟨k * j⁻¹, ⟨K.mul_mem hk (K.inv_mem (hJK hjJ)), ?_⟩, j, hjJ, by group⟩
    have hkjN : k * j⁻¹ ∈ Subgroup.normalizer (L : Set Γ) :=
      mul_mem (hKN hk) (inv_mem hjN)
    refine (d.phi_eq_one_iff (L.mul_mem hkL (L.inv_mem hjL)) hkjN).mp ?_
    have e : (⟨k * j⁻¹, hkjN⟩ : ↥(Subgroup.normalizer (L : Set Γ))) =
        ⟨k, hKN hk⟩ * ⟨j, hjN⟩⁻¹ := rfl
    rw [e, map_mul, map_inv, hjk, mul_inv_cancel]
  have hVN : ⁅N, A⁆ ≤ J := by
    have hle : (⁅N, A⁆ : Subgroup Γ) ≤ N :=
      CFSG.LargeEvenClassification.Helpers.commutator_le_of_normalized N A hAN
    refine hJS _ ⟨hle.trans hNK, ⟨le_top, ?_, ?_⟩, ?_⟩
    · intro q hq
      have hq3 : ¬ 3 ∣ Nat.card (⁅N, A⁆ : Subgroup Γ) := fun h =>
        hN3 (h.trans (Subgroup.card_dvd_of_le hle))
      show (q : ℕ) ≠ 3
      intro h
      exact hq3 (h ▸ hq)
    · exact Subgroup.normalizer_commutator_ge_right N A
    · exact (CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
        Nat.prime_three A N hAp hN3 hAN).symm
  set C : Subgroup Γ := N ⊓ Subgroup.centralizer (A : Set Γ) with hC
  have hCK : C ≤ K := inf_le_left.trans hNK
  have hKCJ : K ≤ C ⊔ J := by
    intro k hk
    obtain ⟨n, hnN, j, hjJ, rfl⟩ := hKNJ k hk
    obtain ⟨f, hf, t, ht, hft⟩ :=
      CFSG.LargeEvenClassification.Helpers.coprime_normalized_fixed_decomposition
        Nat.prime_three A N hAp hN3 hAN ⟨n, hnN⟩
    have hn : n = (f : Γ) * (t : Γ) := by rw [← Subgroup.coe_mul, hft]
    rw [hn, mul_assoc]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨f.2, hf⟩)
      (Subgroup.mem_sup_right (J.mul_mem (hVN ht) hjJ))
  have hCJ : C ≤ Subgroup.normalizer (J : Set Γ) := by
    refine le_normalizer_of_conj_mem fun c hc x hx => ?_
    have hle : J ≤ J.comap (MulAut.conj c).toMonoidHom := by
      refine sSup_le fun V hV => ?_
      obtain ⟨h1, h2, h3'⟩ := conj_mem_signalizers (hNK hc.1) hc.2 hV
      intro v hv
      exact hJS _ ⟨h1, h2, h3'⟩ ⟨v, hv, rfl⟩
    exact hle hx
  have hKNJ' : K ≤ Subgroup.normalizer (J : Set Γ) :=
    hKCJ.trans (sup_le hCJ Subgroup.le_normalizer)
  have hsolC : Group.IsSolvable ↥C := by
    have := isSolvable_thL_sub L
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective ((inf_le_left.trans inf_le_right) : C ≤ thL L))
  exact le_of_perfect_of_le_sup_solvable hKperf hJK hCK hKNJ' hKCJ hsolC

end LRData

end CFSG.RankThree.PartTwo.Sec14.Ronan148B.PS
