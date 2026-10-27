module

public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.RankThree.PartTwo.KFacts.KS44Sz
import CFSG.RankThree.PartTwo.Sec4.Item422KFact
import CFSG.RankThree.GroupTheory.CentralLineComponentAction
import CFSG.RankThree.PartTwo.Sec13.AlphaMonotone
import CFSG.RankThree.Coprime.PlaneCoreCentralizesComponent
import CFSG.RankThree.Coprime.ThetaPlaneNormalizesComponent
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item422Proof

section ThetaNormal

variable {Q : Type*} [Group Q] [Finite Q]

theorem le_inSubgroup_theta_of_normal {S M : Subgroup Q} (hSM : S ≤ M)
    (hS : (S.subgroupOf M).Normal) (hsol : Group.IsSolvable S) (h3 : ¬ 3 ∣ Nat.card S) :
    S ≤ inSubgroup (aschbacherSolvableCore 3) M := by
  let e : S.subgroupOf M ≃* S := Subgroup.subgroupOfEquivOfLe hSM
  have hsol' : Group.IsSolvable (S.subgroupOf M) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have h3' : ¬ 3 ∣ Nat.card (S.subgroupOf M) := by
    rwa [Nat.card_congr e.toEquiv]
  have hle := (solvable_prime_complement_core_characterization (H := M) Nat.prime_three).2.2.2.1
    (S.subgroupOf M) hS hsol' h3'
  have hmap := Subgroup.map_mono (f := M.subtype) hle
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSM] at hmap

theorem inSubgroup_theta_solvable_coprime (N : Subgroup Q) :
    Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) N) ∧
      ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) N) := by
  obtain ⟨hsol, -, h3, -⟩ := solvable_prime_complement_core_characterization (H := N)
    Nat.prime_three
  let e := (aschbacherSolvableCore 3 N).equivMapOfInjective N.subtype N.subtype_injective
  refine ⟨Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective, fun h => h3 ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact h

theorem inSubgroup_theta_le_of_normal {N M : Subgroup Q} (hNM : N ≤ M)
    (hN : (N.subgroupOf M).Normal) :
    inSubgroup (aschbacherSolvableCore 3) N ≤ inSubgroup (aschbacherSolvableCore 3) M := by
  set S := inSubgroup (aschbacherSolvableCore 3) N with hSdef
  have hSN : S ≤ N := Subgroup.map_subtype_le _
  obtain ⟨hsol, h3⟩ := inSubgroup_theta_solvable_coprime N
  refine le_inSubgroup_theta_of_normal (hSN.trans hNM) ?_ hsol h3
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hSN.trans hNM)]
  intro m hm
  have hmN : m ∈ Subgroup.normalizer (N : Set Q) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hN hm
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  have hσ := map_aschbacherSolvableCore (N.normalizerMonoidHom ⟨m, hmN⟩)
  have hmem : (N.normalizerMonoidHom ⟨m, hmN⟩ : N →* N) y ∈ aschbacherSolvableCore 3 N := by
    rw [← hσ]
    exact Subgroup.mem_map_of_mem _ hy
  exact ⟨_, hmem, rfl⟩

end ThetaNormal

theorem map_subgroupOf_normal {W Q : Type*} [Group W] [Group Q] [Finite Q] (φ : W →* Q)
    {A B : Subgroup W} (hAB : A ≤ B) (h : (A.subgroupOf B).Normal) :
    ((A.map φ).subgroupOf (B.map φ)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hAB)]
  rintro _ ⟨b, hb, rfl⟩
  have hbN : b ∈ Subgroup.normalizer (A : Set W) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAB).mp h hb
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨a, ha, rfl⟩ := hy
  exact ⟨b * a * b⁻¹, (Subgroup.mem_normalizer_iff.mp hbN a).mp ha, by
    rw [map_mul, map_mul, map_inv]⟩

theorem map_le_theta_centralizer {W Q : Type*} [Group W] [Group Q] [Finite W] [Finite Q]
    (φ : W →* Q) (hφ : Function.Surjective φ) (b : W) {C₀ K₀ : Subgroup W}
    (hC₀n : C₀.Normal) (hK₀n : K₀.Normal) (hC₀ : C₀ ≤ φ.ker) (hK₀ : K₀ ⊓ φ.ker ≤ C₀)
    (hcomm : ∀ x y : W, x * y * x⁻¹ * y⁻¹ ∈ φ.ker ⊔ K₀) {R : Subgroup W}
    (hRθ : R ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set W)))
    (hRC : R ≤ Subgroup.centralizer (C₀ : Set W)) :
    R.map φ ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({φ b} : Set Q)) := by
  set Cb := Subgroup.centralizer ({b} : Set W) with hCb
  set Θ := inSubgroup (aschbacherSolvableCore 3) Cb with hΘ
  set Zc := Subgroup.centralizer (C₀ : Set W) with hZc
  have hZcn : Zc.Normal := Subgroup.normal_centralizer
  set Rs := Θ ⊓ Zc with hRs
  set D := Cb ⊓ Zc with hD
  set Q₁ : Subgroup W := (Subgroup.centralizer
    ({QuotientGroup.mk' C₀ b} : Set (W ⧸ C₀))).comap (QuotientGroup.mk' C₀) with hQ₁
  set P : Subgroup W := (Subgroup.centralizer ({φ b} : Set Q)).comap φ with hP
  have hQ₁mem : ∀ x : W, x ∈ Q₁ ↔ x * b * x⁻¹ * b⁻¹ ∈ C₀ := by
    intro x
    rw [hQ₁, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    constructor
    · intro h
      have := C₀.inv_mem (hC₀n.conj_mem _ h (b * x))
      convert this using 1
      group
    · intro h
      have := hC₀n.conj_mem _ (C₀.inv_mem h) (b * x)⁻¹
      convert this using 1
      group
  have hPmem : ∀ x : W, x ∈ P ↔ x * b * x⁻¹ * b⁻¹ ∈ φ.ker := by
    intro x
    rw [hP, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, MonoidHom.mem_ker,
      map_mul, map_mul, map_mul, map_inv, map_inv]
    constructor
    · intro h
      rw [h]
      group
    · intro h
      calc φ x * φ b = φ x * φ b * (φ x)⁻¹ * (φ b)⁻¹ * (φ b * φ x) := by group
        _ = φ b * φ x := by rw [h, one_mul]
  have hRRs : R ≤ Rs := le_inf hRθ hRC
  have hΘCb : Θ ≤ Cb := Subgroup.map_subtype_le _
  have hRsD : Rs ≤ D := inf_le_inf_right _ hΘCb
  have hDQ₁ : D ≤ Q₁ := by
    intro x hx
    rw [hQ₁mem]
    have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp hx.1
    rw [hxb, mul_inv_cancel_right, mul_inv_cancel]
    exact C₀.one_mem
  have hQ₁P : Q₁ ≤ P := fun x hx => (hPmem x).mpr (hC₀ ((hQ₁mem x).mp hx))
  have hkerP : φ.ker ≤ P := by
    intro x hx
    rw [hPmem, MonoidHom.mem_ker]
    rw [MonoidHom.mem_ker] at hx
    simp [hx]
  have hN1 : (Rs.subgroupOf D).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hRsD]
    intro d hd
    refine Subgroup.mem_normalizer_fintype fun n hn => ⟨?_, hZcn.conj_mem _ hn.2 d⟩
    obtain ⟨y, hy, rfl⟩ := hn.1
    have hy' : (⟨d, hd.1⟩ : Cb) * y * (⟨d, hd.1⟩ : Cb)⁻¹ ∈ aschbacherSolvableCore 3 Cb :=
      (aschbacherSolvableCore_normal 3 Cb).conj_mem y hy _
    exact ⟨_, hy', rfl⟩
  have hN2 : (D.subgroupOf Q₁).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hDQ₁]
    intro q hq
    refine Subgroup.mem_normalizer_fintype fun d hd => ⟨?_, hZcn.conj_mem _ hd.2 q⟩
    set e := q * d * q⁻¹ with he
    have hdb : d * b = b * d := Subgroup.mem_centralizer_singleton_iff.mp hd.1
    have hA : e * (q * b * q⁻¹) = q * b * q⁻¹ * e := by
      rw [he]
      calc q * d * q⁻¹ * (q * b * q⁻¹) = q * (d * b) * q⁻¹ := by group
        _ = q * (b * d) * q⁻¹ := by rw [hdb]
        _ = q * b * q⁻¹ * (q * d * q⁻¹) := by group
    have hw : q * b * q⁻¹ * b⁻¹ ∈ C₀ := (hQ₁mem q).mp hq
    have hB : q * b * q⁻¹ * b⁻¹ * e = e * (q * b * q⁻¹ * b⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (hZcn.conj_mem _ hd.2 q) _ hw
    have key : q * b * q⁻¹ * (b⁻¹ * e) = q * b * q⁻¹ * (e * b⁻¹) := by
      calc q * b * q⁻¹ * (b⁻¹ * e) = q * b * q⁻¹ * b⁻¹ * e := by group
        _ = e * (q * b * q⁻¹ * b⁻¹) := hB
        _ = e * (q * b * q⁻¹) * b⁻¹ := by group
        _ = q * b * q⁻¹ * e * b⁻¹ := by rw [hA]
        _ = q * b * q⁻¹ * (e * b⁻¹) := by group
    have key' : b⁻¹ * e = e * b⁻¹ := mul_left_cancel key
    change e ∈ Subgroup.centralizer ({b} : Set W)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc e * b = b * (b⁻¹ * e) * b := by group
      _ = b * (e * b⁻¹) * b := by rw [key']
      _ = b * e := by group
  have hQ₁K : Q₁ ⊔ φ.ker ≤ P := sup_le hQ₁P hkerP
  have hN3 : ((Q₁ ⊔ φ.ker).subgroupOf P).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQ₁K]
    intro h hh
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨x, hx, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    have hn' : h * n * h⁻¹ ∈ φ.ker := (MonoidHom.normal_ker φ).conj_mem n hn h
    obtain ⟨c', hc', k, hk, hck⟩ := Subgroup.mem_sup_of_normal_right.mp (hcomm x⁻¹ h)
    have hmP : x⁻¹ * h * x⁻¹⁻¹ * h⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem (P.inv_mem (hQ₁P hx)) hh) (P.inv_mem (P.inv_mem (hQ₁P hx))))
        (P.inv_mem hh)
    have hkP : k ∈ P := by
      have : k = c'⁻¹ * (x⁻¹ * h * x⁻¹⁻¹ * h⁻¹) := by rw [← hck]; group
      rw [this]
      exact P.mul_mem (P.inv_mem (hkerP hc')) hmP
    have hkQ₁ : k ∈ Q₁ := by
      rw [hQ₁mem]
      refine hK₀ ⟨?_, (hPmem k).mp hkP⟩
      have hkb : k * b * k⁻¹ * b⁻¹ = k * (b * k⁻¹ * b⁻¹) := by group
      rw [hkb]
      exact K₀.mul_mem hk (hK₀n.conj_mem _ (K₀.inv_mem hk) b)
    have hconj : h * x * h⁻¹ = x * k * (k⁻¹ * c' * k) := by
      calc h * x * h⁻¹ = x * (x⁻¹ * h * x⁻¹⁻¹ * h⁻¹) := by group
        _ = x * (c' * k) := by rw [hck]
        _ = x * k * (k⁻¹ * c' * k) := by group
    have hmem1 : h * x * h⁻¹ ∈ Q₁ ⊔ φ.ker := by
      rw [hconj]
      exact Subgroup.mul_mem_sup (Q₁.mul_mem hx hkQ₁)
        ((MonoidHom.normal_ker φ).conj_mem' c' hc' k)
    rw [show h * (x * n) * h⁻¹ = h * x * h⁻¹ * (h * n * h⁻¹) by group]
    exact (Q₁ ⊔ φ.ker).mul_mem hmem1 (Subgroup.mem_sup_right hn')
  have hI1 := map_subgroupOf_normal φ hRsD hN1
  have hI2 := map_subgroupOf_normal φ hDQ₁ hN2
  have hI3 := map_subgroupOf_normal φ hQ₁K hN3
  have hsup : (Q₁ ⊔ φ.ker).map φ = Q₁.map φ := by
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff φ.ker).mpr le_rfl, sup_bot_eq]
  rw [hsup] at hI3
  have hPmap : P.map φ = Subgroup.centralizer ({φ b} : Set Q) :=
    Subgroup.map_comap_eq_self_of_surjective hφ _
  rw [hPmap] at hI3
  obtain ⟨hΘsol, hΘ3⟩ := inSubgroup_theta_solvable_coprime Cb
  have hRssol : Group.IsSolvable Rs :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (inf_le_left : Rs ≤ Θ))
  have hRs3 : ¬ 3 ∣ Nat.card Rs := fun h =>
    hΘ3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hsolS : Group.IsSolvable (Rs.map φ) :=
    Group.isSolvable_of_surjective (φ.subgroupMap_surjective Rs)
  have h3S : ¬ 3 ∣ Nat.card (Rs.map φ) := fun h => hRs3 (h.trans (Subgroup.card_map_dvd Rs φ))
  have h1 := le_inSubgroup_theta_of_normal (Subgroup.map_mono hRsD) hI1 hsolS h3S
  have h2 := inSubgroup_theta_le_of_normal (Subgroup.map_mono hDQ₁) hI2
  have hQ₁c : Q₁.map φ ≤ Subgroup.centralizer ({φ b} : Set Q) := by
    rw [← hPmap]
    exact Subgroup.map_mono hQ₁P
  have h3 := inSubgroup_theta_le_of_normal hQ₁c hI3
  exact (Subgroup.map_mono hRRs).trans (h1.trans (h2.trans h3))

section CoreFree

variable {X : Type} [Group X] [Finite X]

theorem centralizer_generalizedFitting_le_pCore (hθ : aschbacherSolvableCore 3 X = ⊥) :
    Subgroup.centralizer (generalizedFitting X : Set X) ≤ CFSG.pCore 3 X := by
  have hCsle : Subgroup.centralizer (generalizedFitting X : Set X) ≤ generalizedFitting X :=
    centralizer_generalizedFitting_le X
  have hchar := (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).1
  have hCsn : (Subgroup.centralizer (generalizedFitting X : Set X)).Normal :=
    Subgroup.normal_centralizer
  have hCscomm : IsMulCommutative (Subgroup.centralizer (generalizedFitting X : Set X)) :=
    ⟨⟨fun x y => Subtype.ext (Subgroup.mem_centralizer_iff.mp x.2 y (hCsle y.2)).symm⟩⟩
  exact (CFSG.LocalCores.fitting_characteristic.2.2 _ hCsn inferInstance).trans
    (fittingSubgroup_le_pCore_of_aschbacherSolvableCore_eq_bot Nat.prime_three hθ)

omit [Finite X] in
theorem conj_comm_mem_centralizer {M : Subgroup X} {c s : X}
    (hc : c ∈ Subgroup.normalizer (M : Set X)) (hs : s ∈ Subgroup.centralizer (M : Set X)) :
    c⁻¹ * (s * c * s⁻¹) ∈ Subgroup.centralizer (M : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hck : c * k * c⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp hc k).mp hk
  have h1 : k * s = s * k := Subgroup.mem_centralizer_iff.mp hs k hk
  have h2 : c * k * c⁻¹ * s = s * (c * k * c⁻¹) := Subgroup.mem_centralizer_iff.mp hs _ hck
  have e1 : s⁻¹ * k = k * s⁻¹ := by
    calc s⁻¹ * k = s⁻¹ * (k * s) * s⁻¹ := by group
      _ = s⁻¹ * (s * k) * s⁻¹ := by rw [h1]
      _ = k * s⁻¹ := by group
  calc k * (c⁻¹ * (s * c * s⁻¹)) = c⁻¹ * (c * k * c⁻¹ * s) * c * s⁻¹ := by group
    _ = c⁻¹ * (s * (c * k * c⁻¹)) * c * s⁻¹ := by rw [h2]
    _ = c⁻¹ * s * c * (k * s⁻¹) := by group
    _ = c⁻¹ * s * c * (s⁻¹ * k) := by rw [e1]
    _ = c⁻¹ * (s * c * s⁻¹) * k := by group

theorem mem_centralizer_of_coprime (hθ : aschbacherSolvableCore 3 X = ⊥) {W C₀ : Subgroup X}
    (hW : ∀ K : Subgroup X, IsComponent K → W ≤ Subgroup.normalizer (K : Set X))
    (hC₀W : C₀ ≤ W) (hWC₀ : W ≤ Subgroup.normalizer (C₀ : Set X)) (𝒮 : Set (Subgroup X))
    (hC₀𝒮 : ∀ K ∈ 𝒮, C₀ ≤ Subgroup.centralizer (K : Set X)) {s : X} (hsW : s ∈ W)
    (hs3 : ¬ 3 ∣ orderOf s) (hsO : s ∈ Subgroup.centralizer (CFSG.pCore 3 X : Set X))
    (hsK : ∀ K : Subgroup X, IsComponent K → K ∉ 𝒮 → s ∈ Subgroup.centralizer (K : Set X)) :
    s ∈ Subgroup.centralizer (C₀ : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have hcW : c ∈ W := hC₀W hc
  set d := c⁻¹ * (s * c * s⁻¹) with hd
  have hscs : s * c * s⁻¹ ∈ C₀ := (Subgroup.mem_normalizer_iff.mp (hWC₀ hsW) c).mp hc
  have hdC₀ : d ∈ C₀ := C₀.mul_mem (C₀.inv_mem hc) hscs
  have hcO : c ∈ Subgroup.normalizer (CFSG.pCore 3 X : Set X) :=
    Subgroup.mem_normalizer_fintype fun n hn => CFSG.pCore_normal.conj_mem n hn c
  have hdO : d ∈ Subgroup.centralizer (CFSG.pCore 3 X : Set X) :=
    conj_comm_mem_centralizer hcO hsO
  have hdK : ∀ K : Subgroup X, IsComponent K → d ∈ Subgroup.centralizer (K : Set X) := by
    intro K hK
    by_cases hK𝒮 : K ∈ 𝒮
    · exact hC₀𝒮 K hK𝒮 hdC₀
    · exact conj_comm_mem_centralizer (hW K hK hcW) (hsK K hK hK𝒮)
  have hdF : d ∈ Subgroup.centralizer (generalizedFitting X : Set X) := by
    have hz : Subgroup.zpowers d ≤ Subgroup.centralizer (generalizedFitting X : Set X) := by
      rw [Subgroup.le_centralizer_iff, generalizedFitting, sup_le_iff]
      constructor
      · refine (fittingSubgroup_le_pCore_of_aschbacherSolvableCore_eq_bot Nat.prime_three
          hθ).trans ?_
        rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
        exact hdO
      · rw [layer, sSup_le_iff]
        intro K hK
        rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
        exact hdK K hK
    exact hz (Subgroup.mem_zpowers d)
  have hdP : d ∈ CFSG.pCore 3 X := centralizer_generalizedFitting_le_pCore hθ hdF
  have hsd : Commute d s := Subgroup.mem_centralizer_iff.mp hsO d hdP
  have hscd : s * c * s⁻¹ = c * d := by rw [hd]; group
  have hpow : ∀ n : ℕ, s ^ n * c * (s ^ n)⁻¹ = c * d ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hdn : s * d ^ n * s⁻¹ = d ^ n := by
        rw [← (hsd.pow_left n).eq]
        group
      calc s ^ (n + 1) * c * (s ^ (n + 1))⁻¹ = s * (s ^ n * c * (s ^ n)⁻¹) * s⁻¹ := by group
        _ = s * (c * d ^ n) * s⁻¹ := by rw [ih]
        _ = (s * c * s⁻¹) * (s * d ^ n * s⁻¹) := by group
        _ = c * d ^ (n + 1) := by rw [hscd, hdn]; group
  have hdn1 : d ^ orderOf s = 1 := by
    have h := hpow (orderOf s)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h
    exact (mul_eq_left.mp h.symm)
  have hdord : orderOf d ∣ orderOf s := orderOf_dvd_of_pow_eq_one hdn1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (p := 3) (G := X)) ⟨d, hdP⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k = 0 := by
    by_contra hk0
    exact hs3 ((dvd_pow_self 3 hk0).trans (hk ▸ hdord))
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  have hscs' : s * c * s⁻¹ = c := by rw [hscd, hk, mul_one]
  calc c * s = s * c * s⁻¹ * s := by rw [hscs']
    _ = s * c := by group

theorem exists_mem_iSup_conj (𝒵 : Set (Subgroup X)) (hcomp : ∀ K ∈ 𝒵, IsComponent K) (g : X)
    (hinner : ∀ K ∈ 𝒵, ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹) :
    ∃ e ∈ ⨆ K ∈ 𝒵, K, ∀ K ∈ 𝒵, e⁻¹ * g ∈ Subgroup.centralizer (K : Set X) := by
  have : Finite (Subgroup X) := Finite.of_injective (fun H : Subgroup X => (H : Set X))
    SetLike.coe_injective
  suffices h : ∀ t : Set (Subgroup X), t.Finite → t ⊆ 𝒵 →
      ∃ e ∈ ⨆ K ∈ t, K, ∀ K ∈ t, e⁻¹ * g ∈ Subgroup.centralizer (K : Set X) from
    h 𝒵 (Set.toFinite 𝒵) le_rfl
  intro t htf
  refine Set.Finite.induction_on (motive := fun t _ => t ⊆ 𝒵 →
      ∃ e ∈ ⨆ K ∈ t, K, ∀ K ∈ t, e⁻¹ * g ∈ Subgroup.centralizer (K : Set X)) t htf ?_ ?_
  · intro _
    exact ⟨1, Subgroup.one_mem _, fun K hK => absurd hK (Set.notMem_empty K)⟩
  · intro a t hat _ ih hsub
    obtain ⟨e, he, hec⟩ := ih ((Set.subset_insert a t).trans hsub)
    have ha𝒵 : a ∈ 𝒵 := hsub (Set.mem_insert a t)
    obtain ⟨k, hk, hka⟩ := hinner a ha𝒵
    have hta : ∀ K ∈ t, K ≤ Subgroup.centralizer (a : Set X) := by
      intro K hK
      rcases CFSG.LocalCores.distinct_components_commute
        (hcomp K (hsub (Set.mem_insert_of_mem a hK))) (hcomp a ha𝒵) with h | h
      · exact absurd (h ▸ hK) hat
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have heC : e ∈ Subgroup.centralizer (a : Set X) := (iSup₂_le hta) he
    refine ⟨e * k, ?_, ?_⟩
    · have hle1 : (⨆ K ∈ t, K) ≤ ⨆ K ∈ insert a t, K :=
        iSup₂_mono' fun K hK => ⟨K, Set.mem_insert_of_mem a hK, le_rfl⟩
      have hle2 : a ≤ ⨆ K ∈ insert a t, K := le_iSup₂_of_le a (Set.mem_insert a t) le_rfl
      exact Subgroup.mul_mem _ (hle1 he) (hle2 hk)
    · intro K hK
      rcases Set.mem_insert_iff.mp hK with rfl | hKt
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hgx := hka x hx
        have hkxk : k * x * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk hx) (K.inv_mem hk)
        have he1 : x * e = e * x := Subgroup.mem_centralizer_iff.mp heC x hx
        have he2 : k * x * k⁻¹ * e = e * (k * x * k⁻¹) :=
          Subgroup.mem_centralizer_iff.mp heC _ hkxk
        have he3 : k * x * k⁻¹ * e⁻¹ = e⁻¹ * (k * x * k⁻¹) := by
          calc k * x * k⁻¹ * e⁻¹ = e⁻¹ * (e * (k * x * k⁻¹)) * e⁻¹ := by group
            _ = e⁻¹ * (k * x * k⁻¹ * e) * e⁻¹ := by rw [he2]
            _ = e⁻¹ * (k * x * k⁻¹) := by group
        calc x * ((e * k)⁻¹ * g) = k⁻¹ * (k * x * k⁻¹ * e⁻¹) * g := by group
          _ = k⁻¹ * (e⁻¹ * (k * x * k⁻¹)) * g := by rw [he3]
          _ = k⁻¹ * e⁻¹ * (g * x * g⁻¹) * g := by rw [hgx]; group
          _ = (e * k)⁻¹ * g * x := by group
      · have hkK : k ∈ Subgroup.centralizer (K : Set X) := by
          have := hta K hKt
          rw [← Subgroup.le_centralizer_iff] at this
          exact this hk
        have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hkK) (hec K hKt)
        rwa [show k⁻¹ * (e⁻¹ * g) = (e * k)⁻¹ * g by group] at this

omit [Finite X] in
theorem exists_inner_of_fixComm {K : Subgroup X}
    (hKF : ∀ z ∈ Subgroup.center K, orderOf z = 3 → ∀ σ τ : MulAut K, σ z = z → τ z = z →
      σ * τ * σ⁻¹ * τ⁻¹ ∈ (MulAut.conj : K →* MulAut K).range)
    {z : X} (hzK : z ∈ K) (hzZ : z ∈ Subgroup.center X) (hz3 : orderOf z = 3) {x y : X}
    (hx : x ∈ Subgroup.normalizer (K : Set X)) (hy : y ∈ Subgroup.normalizer (K : Set X)) :
    ∃ k ∈ K, ∀ w ∈ K, x * y * x⁻¹ * y⁻¹ * w * (x * y * x⁻¹ * y⁻¹)⁻¹ = k * w * k⁻¹ := by
  set σ := K.normalizerMonoidHom ⟨x, hx⟩ with hσ
  set τ := K.normalizerMonoidHom ⟨y, hy⟩ with hτ
  have hz' : (⟨z, hzK⟩ : K) ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun w =>
    Subtype.ext (Subgroup.mem_center_iff.mp hzZ w)
  have hzo : orderOf (⟨z, hzK⟩ : K) = 3 := by rw [Subgroup.orderOf_mk]; exact hz3
  have hfix : ∀ g (hg : g ∈ Subgroup.normalizer (K : Set X)),
      K.normalizerMonoidHom ⟨g, hg⟩ ⟨z, hzK⟩ = ⟨z, hzK⟩ := by
    intro g hg
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_coe]
    have := Subgroup.mem_center_iff.mp hzZ g
    rw [this]
    group
  obtain ⟨k, hk⟩ := hKF ⟨z, hzK⟩ hz' hzo σ τ (hfix x hx) (hfix y hy)
  have hcomm : σ * τ * σ⁻¹ * τ⁻¹ = K.normalizerMonoidHom
      (⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : Subgroup.normalizer (K : Set X))⁻¹ *
        (⟨y, hy⟩ : Subgroup.normalizer (K : Set X))⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  refine ⟨k, k.2, fun w hw => ?_⟩
  have h := congrArg (fun φ : MulAut K => ((φ ⟨w, hw⟩ : K) : X)) (hk.trans hcomm)
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
  rw [normalizerMonoidHom_apply_coe] at h
  exact h.symm

theorem exists_orderOf_eq_mem_centralizer {p : ℕ} [Fact p.Prime] {P K : Subgroup X}
    (hP : IsPGroup p P) (hPK : P ≤ Subgroup.normalizer (K : Set X)) (hpK : p ∣ Nat.card K) :
    ∃ u ∈ K, u ∈ Subgroup.centralizer (P : Set X) ∧ orderOf u = p := by
  let f : P →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion hPK)
  let _ : MulAction P K := MulAction.compHom K f
  have hfix := hP.card_modEq_card_fixedPoints K
  set F := (Subgroup.centralizer (P : Set X)).subgroupOf K with hFdef
  have hF : MulAction.fixedPoints P K = (F : Set K) := by
    ext k
    rw [MulAction.mem_fixedPoints, SetLike.mem_coe, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h x hx
      have h' := congrArg Subtype.val (h ⟨x, hx⟩)
      change x * (k : X) * x⁻¹ = k at h'
      calc x * (k : X) = x * k * x⁻¹ * x := by group
        _ = k * x := by rw [h']
    · intro h x
      apply Subtype.ext
      change (x : X) * k * (x : X)⁻¹ = k
      rw [h x x.2]
      group
  have hdvd : p ∣ Nat.card F := by
    have h1 : Nat.card (MulAction.fixedPoints P K) = Nat.card F := by rw [hF]; rfl
    rw [← h1]
    apply Nat.dvd_of_mod_eq_zero
    have h2 : Nat.card K % p = 0 := Nat.mod_eq_zero_of_dvd hpK
    unfold Nat.ModEq at hfix
    rw [← hfix, h2]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := F) p hdvd
  refine ⟨((u : K) : X), (u : K).2, Subgroup.mem_subgroupOf.mp u.2, ?_⟩
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hu]

end CoreFree

section Automizer

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem autIn_eq_range {U K : Subgroup X} (hU : U ≤ Subgroup.normalizer (K : Set X)) :
    autIn U K = (K.normalizerMonoidHom.comp (Subgroup.inclusion hU)).range := by
  ext σ
  rw [mem_autIn_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨h, hN, hH, rfl⟩
    exact ⟨⟨h, hH⟩, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, hU u.2, u.2, rfl⟩

omit [Finite X] in
theorem autIn_mono {U U' K : Subgroup X} (h : U ≤ U') : autIn U K ≤ autIn U' K := by
  intro σ hσ
  obtain ⟨g, hN, hg, rfl⟩ := mem_autIn_iff.mp hσ
  exact mem_autIn_iff.mpr ⟨g, hN, h hg, rfl⟩

omit [Finite X] in
theorem card_autIn_mul_card_inf {U K : Subgroup X} (hU : U ≤ Subgroup.normalizer (K : Set X)) :
    Nat.card (autIn U K) * Nat.card (U ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) =
      Nat.card U := by
  set f := K.normalizerMonoidHom.comp (Subgroup.inclusion hU) with hf
  have hker : f.ker = (Subgroup.centralizer (K : Set X)).subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  have hcardker :
      Nat.card f.ker = Nat.card (U ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) := by
    rw [hker, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [autIn_eq_range hU, ← hcardker,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm

omit [Finite X] in
theorem isElemAbelian_autIn {U K : Subgroup X} (hU : CFSG.Assembly.IsElemAbelian 3 U) :
    CFSG.Assembly.IsElemAbelian 3 (autIn U K) := by
  refine ⟨⟨⟨fun σ τ => ?_⟩⟩, fun σ hσ => ?_⟩
  · obtain ⟨g, hgN, hgU, hg⟩ := mem_autIn_iff.mp σ.2
    obtain ⟨h, hhN, hhU, hh⟩ := mem_autIn_iff.mp τ.2
    apply Subtype.ext
    change (σ : MulAut K) * τ = τ * σ
    rw [← hg, ← hh, ← map_mul, ← map_mul]
    have hgh : g * h = h * g := congrArg Subtype.val (hU.1.is_comm.comm ⟨g, hgU⟩ ⟨h, hhU⟩)
    congr 1
    exact Subtype.ext hgh
  · obtain ⟨g, hgN, hgU, rfl⟩ := mem_autIn_iff.mp hσ
    rw [← map_pow]
    have : (⟨g, hgN⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hU.2 g hgU)
    rw [this, map_one]

theorem inf_centralizer_ne_bot_of_not_three_dvd (hSz : KFacts.KPSz)
    (hKX : CFSG.IsKGroup X) {Bb K : Subgroup X} (hBb : CFSG.Assembly.IsElemAbelian 3 Bb)
    (hBcard : Nat.card Bb = 9) (hK : IsComponent K) (hBN : Bb ≤ Subgroup.normalizer (K : Set X))
    (h3 : ¬ 3 ∣ Nat.card (K ⧸ Subgroup.center K)) :
    Bb ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ := by
  intro hbot
  have hcard : Nat.card (autIn Bb K) = 9 := by
    have := card_autIn_mul_card_inf hBN
    rwa [hbot, Subgroup.card_bot, mul_one, hBcard] at this
  have hcat : CFSG.Assembly.InCatalog (K ⧸ Subgroup.center K) :=
    hKX K (Subgroup.center K) hK.1.2.1
  exact false_of_elemAbelian_nine_le_mulAut hSz hK.1 hcat h3 (autIn Bb K)
    (isElemAbelian_autIn hBb) hcard

theorem mem_component_of_three_dvd {Ab Bb K₁ K : Subgroup X} {cb : X}
    (hmaxX : ∀ u : X, u ^ 3 = 1 → u ∈ Subgroup.centralizer (Ab : Set X) → u ∈ Ab)
    (hABZ : Ab = Bb ⊔ Subgroup.zpowers cb) (hcbZ : cb ∈ Subgroup.center X)
    (hcb3 : orderOf cb = 3) (hK₁ : IsComponent K₁)
    (hfaith : ∀ x ∈ Ab, x ∈ Subgroup.centralizer (K₁ : Set X) ↔ x ∈ Subgroup.zpowers cb)
    (hBbp : IsPGroup 3 Bb) (hK : IsComponent K) (hKK₁ : K ≠ K₁)
    (hBN : Bb ≤ Subgroup.normalizer (K : Set X)) (h3 : 3 ∣ Nat.card K) : cb ∈ K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, huK, huC, hu3⟩ := exists_orderOf_eq_mem_centralizer hBbp hBN h3
  have hu3' : u ^ 3 = 1 := by rw [← hu3]; exact pow_orderOf_eq_one u
  have huA : u ∈ Subgroup.centralizer (Ab : Set X) := by
    have hz : Subgroup.zpowers u ≤ Subgroup.centralizer (Ab : Set X) := by
      rw [Subgroup.le_centralizer_iff, hABZ, sup_le_iff]
      constructor
      · rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
        exact huC
      · rw [Subgroup.zpowers_le]
        exact Subgroup.center_le_centralizer _ hcbZ
    exact hz (Subgroup.mem_zpowers u)
  have huAb := hmaxX u hu3' huA
  have huK₁ : u ∈ Subgroup.centralizer (K₁ : Set X) := by
    rcases CFSG.LocalCores.distinct_components_commute hK hK₁ with h | h
    · exact absurd h hKK₁
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h huK
  have huz := (hfaith u huAb).mp huK₁
  have hle : Subgroup.zpowers u ≤ Subgroup.zpowers cb := Subgroup.zpowers_le.mpr huz
  have heq : Subgroup.zpowers u = Subgroup.zpowers cb :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hu3, hcb3])
  have hcbu : cb ∈ Subgroup.zpowers u := heq ▸ Subgroup.mem_zpowers cb
  exact (Subgroup.zpowers_le.mpr huK) hcbu

theorem mem_normalizer_centralizer {K : Subgroup X} {w : X}
    (hw : w ∈ Subgroup.normalizer (K : Set X)) :
    w ∈ Subgroup.normalizer (Subgroup.centralizer (K : Set X) : Set X) := by
  refine Subgroup.mem_normalizer_fintype fun c hc => ?_
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hc ⊢
  intro k hk
  have hk' : w⁻¹ * k * w⁻¹⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hw) k).mp hk
  have := hc _ hk'
  calc k * (w * c * w⁻¹) = w * (w⁻¹ * k * w⁻¹⁻¹ * c) * w⁻¹ := by group
    _ = w * (c * (w⁻¹ * k * w⁻¹⁻¹)) * w⁻¹ := by rw [this]
    _ = w * c * w⁻¹ * k := by group

omit [Finite X] in
theorem commutator_subgroupOf {A B W : Subgroup X} (hA : A ≤ W) (hB : B ≤ W) :
    ⁅A.subgroupOf W, B.subgroupOf W⁆ = (⁅A, B⁆ : Subgroup X).subgroupOf W := by
  apply Subgroup.map_injective W.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA, inf_eq_left.mpr hB, inf_eq_left.mpr]
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [commutatorElement_def]
  exact W.mul_mem (W.mul_mem (W.mul_mem (hA hg) (hB hh)) (W.inv_mem (hA hg))) (W.inv_mem (hB hh))

theorem subgroupOf_theta_le {W : Subgroup X} {b : X} (hbW : b ∈ W) :
    (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X))).subgroupOf W ≤
      inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({(⟨b, hbW⟩ : W)} : Set W)) := by
  set R := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X)) with hR
  set Cb := Subgroup.centralizer ({b} : Set X) with hCb
  have hRC : R ≤ Cb := Subgroup.map_subtype_le _
  obtain ⟨hRsol, hR3⟩ := inSubgroup_theta_solvable_coprime Cb
  have hle : R.subgroupOf W ≤ Subgroup.centralizer ({(⟨b, hbW⟩ : W)} : Set W) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
      (hRC (Subgroup.mem_subgroupOf.mp hx)))
  let ι : R.subgroupOf W →* R :=
    { toFun := fun x => ⟨((x : W) : X), Subgroup.mem_subgroupOf.mp x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun x y h => by
    have h' : ((ι x : R) : X) = ((ι y : R) : X) := congrArg (fun r : R => (r : X)) h
    apply Subtype.ext
    apply Subtype.ext
    exact h'
  refine le_inSubgroup_theta_of_normal hle ?_ (Group.isSolvable_of_isSolvable_injective hι)
    (fun h => hR3 (h.trans (Subgroup.card_dvd_of_injective ι hι)))
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  intro c hc
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  simp only [SetLike.mem_coe] at hx ⊢
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have hcX : ((c : W) : X) ∈ Cb := Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc))
  obtain ⟨y, hy, hyx⟩ := hx
  have hy' : (⟨(c : X), hcX⟩ : Cb) * y * (⟨(c : X), hcX⟩ : Cb)⁻¹ ∈
      aschbacherSolvableCore 3 Cb := (aschbacherSolvableCore_normal 3 Cb).conj_mem y hy _
  refine ⟨_, hy', ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hyx ⊢
  rw [hyx]

theorem thetaAlpha_ne_bot_of_le' {M : Type*} [Group M] [Finite M] {B N Y : Subgroup M}
    (hBN : B ≤ N) (hNY : N ≤ Y) (hN : (N.subgroupOf Y).Normal)
    (h : thetaAlpha 3 (B.subgroupOf N) ≠ ⊥) : thetaAlpha 3 (B.subgroupOf Y) ≠ ⊥ := by
  refine Sec13.thetaAlpha_ne_bot_of_subgroupOf hN (fun x hx => Subgroup.mem_subgroupOf.mpr
    (hBN (Subgroup.mem_subgroupOf.mp hx))) ?_
  let e : (N.subgroupOf Y) ≃* N := Subgroup.subgroupOfEquivOfLe hNY
  have he : ((B.subgroupOf Y).subgroupOf (N.subgroupOf Y)).map e.toMonoidHom =
      B.subgroupOf N := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp
        (Subgroup.mem_subgroupOf.mp hz))
    · intro hy
      refine ⟨e.symm y, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_), by simp⟩
      exact Subgroup.mem_subgroupOf.mp hy
  intro hbot
  apply h
  rw [← he, ← thetaAlpha_map_equiv Nat.prime_three, hbot, Subgroup.map_bot]

end Automizer

section Transfer

variable {X : Type} [Group X] [Finite X]

theorem thetaAlpha_autIn_ne_bot_of_fixComm
    (hKF : ∀ K L : Subgroup X, IsComponent K → IsComponent L → K ≠ L →
      ∀ z ∈ Subgroup.center K, orderOf z = 3 → ∀ σ τ : MulAut K, σ z = z → τ z = z →
        σ * τ * σ⁻¹ * τ⁻¹ ∈ (MulAut.conj : K →* MulAut K).range)
    (hSz : KFacts.KPSz) (hθ : aschbacherSolvableCore 3 X = ⊥) (hKX : CFSG.IsKGroup X)
    {Ab Bb : Subgroup X} {cb : X} (hcbZ : cb ∈ Subgroup.center X) (hcb3 : orderOf cb = 3)
    (hBb : CFSG.Assembly.IsElemAbelian 3 Bb) (hBcard : Nat.card Bb = 9)
    (hBZ : Bb ⊓ Subgroup.zpowers cb = ⊥) (hABZ : Ab = Bb ⊔ Subgroup.zpowers cb)
    (hmaxX : ∀ u : X, u ^ 3 = 1 → u ∈ Subgroup.centralizer (Ab : Set X) → u ∈ Ab)
    (hAN : ∀ K : Subgroup X, IsComponent K → Ab ≤ Subgroup.normalizer (K : Set X))
    {K₁ : Subgroup X} (hK₁ : IsComponent K₁)
    (hfaith : ∀ x ∈ Ab, x ∈ Subgroup.centralizer (K₁ : Set X) ↔ x ∈ Subgroup.zpowers cb)
    (hQ : ¬ thetaAlpha 3 Bb ≤ Subgroup.centralizer (K₁ : Set X)) :
    thetaAlpha 3 ((autIn Ab K₁).subgroupOf (autIn ⊤ K₁)) ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut K₁) := Finite.of_injective (fun σ : MulAut K₁ => (σ : K₁ → K₁))
    (fun σ τ h => MulEquiv.ext (congrFun h))
  have hBA : Bb ≤ Ab := hABZ ▸ le_sup_left
  have hBbp : IsPGroup 3 Bb := fun x => ⟨1, Subtype.ext (by simpa using hBb.2 x x.2)⟩
  have hBbE : IsElementaryAbelian 3 Bb :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 Bb).mpr hBb
  have hBcard' : Nat.card Bb = 3 ^ 2 := by rw [hBcard]; norm_num
  have hBN : ∀ K : Subgroup X, IsComponent K → Bb ≤ Subgroup.normalizer (K : Set X) :=
    fun K hK => hBA.trans (hAN K hK)
  have hBK₁ : Bb ⊓ Subgroup.centralizer (K₁ : Set X) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxz := (hfaith x (hBA hx.1)).mp hx.2
    have hmem : x ∈ Bb ⊓ Subgroup.zpowers cb := ⟨hx.1, hxz⟩
    rwa [hBZ] at hmem
  have hBne : Bb ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hBcard
    norm_num at hBcard
  obtain ⟨⟨b₀, hb₀⟩, hb₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hb₀1' : b₀ ≠ 1 := fun h => hb₀1 (Subtype.ext h)
  have hcomm₁ : ∀ K : Subgroup X, IsComponent K → K ≠ K₁ →
      K ≤ Subgroup.centralizer (K₁ : Set X) := by
    intro K hK hKK₁
    rcases CFSG.LocalCores.distinct_components_commute hK hK₁ with h | h
    · exact absurd h hKK₁
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  set 𝒵 : Set (Subgroup X) :=
    {K | IsComponent K ∧ K ≠ K₁ ∧ Bb ⊓ Subgroup.centralizer (K : Set X) = ⊥} with h𝒵
  have h𝒵c : ∀ K ∈ 𝒵, cb ∈ K := by
    intro K hK
    have h3 : 3 ∣ Nat.card (K ⧸ Subgroup.center K) := by
      by_contra h
      exact inf_centralizer_ne_bot_of_not_three_dvd hSz hKX hBb hBcard hK.1 (hBN K hK.1) h hK.2.2
    exact mem_component_of_three_dvd hmaxX hABZ hcbZ hcb3 hK₁ hfaith hBbp hK.1 hK.2.1
      (hBN K hK.1) (h3.trans (Subgroup.card_quotient_dvd_card _))
  set W : Subgroup X := ⨅ (K : Subgroup X) (_ : IsComponent K), Subgroup.normalizer (K : Set X)
    with hW
  have hWn : W.Normal := iInf_normalizer_components_normal
  have hWN : ∀ K : Subgroup X, IsComponent K → W ≤ Subgroup.normalizer (K : Set X) :=
    fun K hK => iInf₂_le K hK
  have hmemW : ∀ g : X, (∀ K : Subgroup X, IsComponent K →
      g ∈ Subgroup.normalizer (K : Set X)) → g ∈ W := by
    intro g hg
    simp only [hW, Subgroup.mem_iInf]
    exact hg
  have hBW : Bb ≤ W := fun x hx => hmemW x fun K hK => hBN K hK hx
  have hcbW : cb ∈ W := hmemW cb fun K _ => Subgroup.mem_normalizer_fintype fun n _ => by
    rw [← Subgroup.mem_center_iff.mp hcbZ n]
    group
    exact ‹n ∈ (K : Set X)›
  have hAW : Ab ≤ W := by
    rw [hABZ]
    exact sup_le hBW (Subgroup.zpowers_le.mpr hcbW)
  have hcompW : ∀ K : Subgroup X, IsComponent K → K ≤ W := by
    intro K hK x hx
    apply hmemW x
    intro K' hK'
    rcases CFSG.LocalCores.distinct_components_commute hK hK' with h | h
    · exact h ▸ Subgroup.le_normalizer hx
    · exact Subgroup.centralizer_le_normalizer _
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx)
  set R : X → Subgroup X := fun b =>
    inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X)) with hR
  set T := thetaT 3 Bb with hT
  have hRn : ∀ b : X, ((R b).subgroupOf (Subgroup.centralizer ({b} : Set X))).Normal := by
    intro b
    rw [show (R b).subgroupOf (Subgroup.centralizer ({b} : Set X)) =
      aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set X)) from
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _]
    infer_instance
  have hRC : ∀ b : X, R b ≤ Subgroup.centralizer ({b} : Set X) :=
    fun b => Subgroup.map_subtype_le _
  have hRBb : ∀ b ∈ Bb, Bb ≤ Subgroup.normalizer (R b : Set X) := by
    intro b hb
    have hBC : Bb ≤ Subgroup.centralizer ({b} : Set X) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hBb.1.is_comm.comm (⟨x, hx⟩ : Bb) ⟨b, hb⟩))
    exact hBC.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (hRC b)).mp (hRn b))
  have hVR : ∀ b ∈ Bb, ⁅R b, Bb⁆ ≤ R b := fun b hb =>
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hRBb b hb)
  have hTR : ∀ b ∈ Bb, b ≠ 1 → T ≤ R b := fun b hb hb1 =>
    iInf₂_le_of_le b hb (iInf_le _ hb1)
  have hR3 : ∀ b : X, ¬ 3 ∣ Nat.card (R b) := fun b =>
    (inSubgroup_theta_solvable_coprime _).2
  have hRo : ∀ b : X, ∀ x ∈ R b, ¬ 3 ∣ orderOf x := fun b x hx h =>
    hR3 b (h.trans (Subgroup.orderOf_dvd_natCard _ hx))
  have hRO : ∀ b ∈ Bb, R b ≤ Subgroup.centralizer (CFSG.pCore 3 X : Set X) := by
    intro b hb
    have hbp : IsPGroup 3 (Subgroup.zpowers b) := hBbp.to_le (Subgroup.zpowers_le.mpr hb)
    have hzc : Subgroup.centralizer ((Subgroup.zpowers b : Subgroup X) : Set X) =
        Subgroup.centralizer ({b} : Set X) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hRP : ⁅R b, CFSG.pCore 3 X⁆ = ⊥ :=
      local_prime_complement_centralizes_normal_prime_group Nat.prime_three
        (P := CFSG.pCore 3 X) (A := Subgroup.zpowers b) (S := R b) CFSG.pCore_isPGroup hbp
        (by rw [hzc]; exact hRC b) (by rw [hzc]; exact hRn b) (hR3 b)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRP
  have hNF : ∀ K : Subgroup X, IsComponent K → Bb ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ →
      ∀ b ∈ Bb, b ≠ 1 → ⁅R b, Bb⁆ ≤ Subgroup.centralizer (K : Set X) ∧
        T ≤ Subgroup.centralizer (K : Set X) := by
    intro K hK hne b hb hb1
    obtain ⟨h1, h2, -⟩ := Coprime.nonfaithful_plane_local_core_product_centralizes_component
      Nat.prime_three hBbE hBcard' hb hb1 hK (commutator_le_normalizer_of_components hBN hK) hne
    exact ⟨Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1,
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2⟩
  have hVW : ∀ b : X, ⁅R b, Bb⁆ ≤ W := fun b x hx =>
    hmemW x fun K hK => commutator_le_normalizer_of_components hBN hK hx
  have hTW : T ≤ W := by
    intro x hx
    apply hmemW x
    intro K hK
    by_cases h3 : 3 ∣ Nat.card (K ⧸ Subgroup.center K)
    · exact Coprime.theta_plane_intersection_normalizes_prime_component Nat.prime_three hK
        (center_component_le_pCore Nat.prime_three hθ hK) h3 (hBN K hK) hBbE hBcard' hx
    · exact Subgroup.centralizer_le_normalizer _ ((hNF K hK
        (inf_centralizer_ne_bot_of_not_three_dvd hSz hKX hBb hBcard hK (hBN K hK) h3)
        b₀ hb₀ hb₀1').2 hx)
  set K₀ : Subgroup X := ⨅ K ∈ 𝒵, Subgroup.centralizer (K : Set X) with hK₀
  have hmemK₀ : ∀ g : X, g ∈ K₀ ↔ ∀ K ∈ 𝒵, g ∈ Subgroup.centralizer (K : Set X) := by
    intro g
    simp only [hK₀, Subgroup.mem_iInf]
  set C₀X : Subgroup X := W ⊓ (Subgroup.centralizer (K₁ : Set X) ⊓ K₀) with hC₀X
  have hWK₀ : W ≤ Subgroup.normalizer (K₀ : Set X) := by
    intro w hw
    refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    rw [SetLike.mem_coe, hmemK₀] at hk ⊢
    intro K hK
    exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer (hWN K hK.1 hw)) k).mp
      (hk K hK)
  have hWC₀ : W ≤ Subgroup.normalizer (C₀X : Set X) := by
    intro w hw
    refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    obtain ⟨hkW, hkC, hkK₀⟩ := hk
    refine ⟨hWn.conj_mem k hkW w, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer (hWN K₁ hK₁ hw)) k).mp
        hkC
    · exact (Subgroup.mem_normalizer_iff.mp (hWK₀ hw) k).mp hkK₀
  have hC₀𝒮 : ∀ K ∈ insert K₁ 𝒵, C₀X ≤ Subgroup.centralizer (K : Set X) := by
    intro K hK x hx
    rcases Set.mem_insert_iff.mp hK with rfl | hK𝒵
    · exact hx.2.1
    · exact (hmemK₀ x).mp hx.2.2 K hK𝒵
  have hpiece : ∀ b ∈ Bb, b ≠ 1 → ∀ s : X, s ∈ W → s ∈ R b →
      (∀ K : Subgroup X, IsComponent K → Bb ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ →
        s ∈ Subgroup.centralizer (K : Set X)) → s ∈ Subgroup.centralizer (C₀X : Set X) := by
    intro b hb _ s hsW hsR hsK
    refine mem_centralizer_of_coprime hθ hWN inf_le_left hWC₀ (insert K₁ 𝒵) hC₀𝒮 hsW
      (hRo b s hsR) (hRO b hb hsR) fun K hK hK𝒮 => hsK K hK fun hbot => hK𝒮 ?_
    exact Set.mem_insert_of_mem _ ⟨hK, fun h => hK𝒮 (h ▸ Set.mem_insert _ _), hbot⟩
  have hWK₁ : W ≤ Subgroup.normalizer (K₁ : Set X) := hWN K₁ hK₁
  set ψ : W →* MulAut K₁ := K₁.normalizerMonoidHom.comp (Subgroup.inclusion hWK₁) with hψ
  have hY : autIn W K₁ = ψ.range := autIn_eq_range hWK₁
  have hψmem : ∀ w : W, ψ w ∈ autIn W K₁ := fun w => by rw [hY]; exact ⟨w, rfl⟩
  set φ : W →* autIn W K₁ := ψ.codRestrict (autIn W K₁) hψmem with hφ
  have hφs : Function.Surjective φ := by
    rintro ⟨σ, hσ⟩
    rw [hY] at hσ
    obtain ⟨w, rfl⟩ := hσ
    exact ⟨w, rfl⟩
  have hφker : ∀ w : W, w ∈ φ.ker ↔ (w : X) ∈ Subgroup.centralizer (K₁ : Set X) := by
    intro w
    have hiff : φ w = 1 ↔ ψ w = 1 := ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [MonoidHom.mem_ker, hiff, hψ, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    rfl
  set K₀' : Subgroup W := K₀.subgroupOf W with hK₀'
  have hK₀'n : K₀'.Normal := ⟨fun k hk w => by
    rw [hK₀', Subgroup.mem_subgroupOf] at hk ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hWK₀ w.2) k).mp hk⟩
  have hkern : φ.ker.Normal := MonoidHom.normal_ker φ
  set C₀' : Subgroup W := φ.ker ⊓ K₀' with hC₀'
  have hC₀'n : C₀'.Normal := Subgroup.normal_inf_normal _ _
  have hK₀'C : K₀' ⊓ φ.ker ≤ C₀' := by rw [hC₀', inf_comm]
  have hcommW : ∀ x y : W, x * y * x⁻¹ * y⁻¹ ∈ φ.ker ⊔ K₀' := by
    intro x y
    set g : X := (x : X) * y * (x : X)⁻¹ * (y : X)⁻¹ with hg
    have hinner : ∀ K ∈ 𝒵, ∃ k ∈ K, ∀ w ∈ K, g * w * g⁻¹ = k * w * k⁻¹ := fun K hK =>
      exists_inner_of_fixComm (hKF K K₁ hK.1 hK₁ hK.2.1) (h𝒵c K hK) hcbZ hcb3 (hWN K hK.1 x.2)
        (hWN K hK.1 y.2)
    obtain ⟨e, he, hec⟩ := exists_mem_iSup_conj 𝒵 (fun K hK => hK.1) g hinner
    have heW : e ∈ W := (iSup₂_le fun K hK => hcompW K hK.1) he
    have heK₁ : e ∈ Subgroup.centralizer (K₁ : Set X) :=
      (iSup₂_le fun K hK => hcomm₁ K hK.1 hK.2.1) he
    have h1 : (⟨e, heW⟩ : W) ∈ φ.ker := (hφker _).mpr heK₁
    have h2 : (⟨e, heW⟩ : W)⁻¹ * (x * y * x⁻¹ * y⁻¹) ∈ K₀' := by
      rw [hK₀', Subgroup.mem_subgroupOf, hmemK₀]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      intro K hK
      exact hec K hK
    have := Subgroup.mul_mem_sup h1 h2
    rwa [mul_inv_cancel_left] at this
  have hGL : ∀ P : Subgroup X, P ≤ W → ∀ b' : W, (b' : X) ∈ Bb → (b' : X) ≠ 1 →
      P ≤ R (b' : X) →
      (∀ s ∈ P, ∀ K : Subgroup X, IsComponent K → Bb ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ →
        s ∈ Subgroup.centralizer (K : Set X)) →
      (P.subgroupOf W).map φ ≤ inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({φ b'} : Set (autIn W K₁))) := by
    intro P hPW b' hb' hb'1 hPR hPK
    refine map_le_theta_centralizer φ hφs b' hC₀'n hK₀'n inf_le_left hK₀'C hcommW ?_ ?_
    · have hle : P.subgroupOf W ≤ (R (b' : X)).subgroupOf W := fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hPR (Subgroup.mem_subgroupOf.mp hx))
      exact hle.trans (subgroupOf_theta_le b'.2)
    · intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hcX : (c : X) ∈ C₀X :=
        ⟨c.2, (hφker c).mp hc.1, Subgroup.mem_subgroupOf.mp hc.2⟩
      have hsX := Subgroup.mem_subgroupOf.mp hs
      have := Subgroup.mem_centralizer_iff.mp
        (hpiece _ hb' hb'1 _ (hPW hsX) (hPR hsX) (hPK _ hsX)) _ hcX
      exact Subtype.ext this
  have hzN : (Subgroup.zpowers cb).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcbZ)
  set B₃ : Subgroup (autIn W K₁) := (autIn Ab K₁).subgroupOf (autIn W K₁) with hB₃def
  have hB₃ : B₃ = (Bb.subgroupOf W).map φ := by
    ext β
    rw [hB₃def, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · intro hβ
      obtain ⟨g, hgN, hgA, hg⟩ := mem_autIn_iff.mp hβ
      rw [hABZ] at hgA
      obtain ⟨b', hb', z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hgA
      refine ⟨⟨b', hBW hb'⟩, Subgroup.mem_subgroupOf.mpr hb', ?_⟩
      apply Subtype.ext
      rw [← hg]
      ext k
      change (b' : X) * k * b'⁻¹ = b' * z * k * (b' * z)⁻¹
      have hzk : z * k = k * z := (Subgroup.mem_center_iff.mp
        (Subgroup.zpowers_le.mpr hcbZ hz) k).symm
      calc (b' : X) * k * b'⁻¹ = b' * (k * z) * z⁻¹ * b'⁻¹ := by group
        _ = b' * (z * k) * z⁻¹ * b'⁻¹ := by rw [hzk]
        _ = b' * z * k * (b' * z)⁻¹ := by group
    · rintro ⟨b', hb', rfl⟩
      exact mem_autIn_iff.mpr ⟨b', hWK₁ b'.2, hBA (Subgroup.mem_subgroupOf.mp hb'), rfl⟩
  have hnormal : ((autIn W K₁).subgroupOf (autIn ⊤ K₁)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (autIn_mono le_top)]
    intro σ hσ
    obtain ⟨n, hnN, -, rfl⟩ := mem_autIn_iff.mp hσ
    refine Subgroup.mem_normalizer_fintype fun τ hτ => ?_
    obtain ⟨w, hwN, hwW, rfl⟩ := mem_autIn_iff.mp hτ
    refine mem_autIn_iff.mpr ⟨n * w * n⁻¹, ?_, hWn.conj_mem w hwW n, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnN hwN) (Subgroup.inv_mem _ hnN)
    · rw [← map_inv, ← map_mul, ← map_mul]
      rfl
  refine thetaAlpha_ne_bot_of_le' (autIn_mono hAW) (autIn_mono le_top) hnormal ?_
  change thetaAlpha 3 B₃ ≠ ⊥
  by_cases hTK : T ≤ Subgroup.centralizer (K₁ : Set X)
  ·
    have hJ : ¬ thetaJ 3 Bb ≤ Subgroup.centralizer (K₁ : Set X) := fun h =>
      hQ (by rw [thetaAlpha]; exact sup_le h hTK)
    obtain ⟨b, hb, hb1, hVK⟩ : ∃ b ∈ Bb, b ≠ 1 ∧
        ¬ ⁅R b, Bb⁆ ≤ Subgroup.centralizer (K₁ : Set X) := by
      by_contra hcon
      push Not at hcon
      exact hJ (iSup₂_le fun b hb => iSup_le fun hb1 => hcon b hb hb1)
    set b' : W := ⟨b, hBW hb⟩ with hb'
    have hVne : ((⁅R b, Bb⁆ : Subgroup X).subgroupOf W).map φ ≠ ⊥ := by
      intro hbot
      apply hVK
      intro v hv
      have hmem : φ ⟨v, hVW b hv⟩ ∈ ((⁅R b, Bb⁆ : Subgroup X).subgroupOf W).map φ :=
        Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hv)
      rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, hφker] at hmem
      exact hmem
    have hVle := hGL _ (hVW b) b' hb hb1 (hVR b hb) fun s hs K hK hne =>
      (hNF K hK hne b hb hb1).1 hs
    have hβB : φ b' ∈ B₃ := hB₃ ▸ ⟨b', Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    have hβ1 : φ b' ≠ 1 := by
      intro h
      have hk : b' ∈ φ.ker := h
      rw [hφker] at hk
      have hmem : b ∈ Bb ⊓ Subgroup.centralizer (K₁ : Set X) := ⟨hb, hk⟩
      rw [hBK₁] at hmem
      exact hb1 hmem
    have hidem : ⁅⁅R b, Bb⁆, Bb⁆ = ⁅R b, Bb⁆ :=
      CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
        Nat.prime_three Bb (R b) hBbp (hR3 b) (hRBb b hb)
    have hcomm' : ⁅(⁅R b, Bb⁆ : Subgroup X).subgroupOf W, Bb.subgroupOf W⁆ =
        (⁅R b, Bb⁆ : Subgroup X).subgroupOf W := by
      rw [commutator_subgroupOf (hVW b) hBW, hidem]
    have hJle : ((⁅R b, Bb⁆ : Subgroup X).subgroupOf W).map φ ≤ thetaJ 3 B₃ := by
      calc ((⁅R b, Bb⁆ : Subgroup X).subgroupOf W).map φ =
            ⁅((⁅R b, Bb⁆ : Subgroup X).subgroupOf W).map φ, (Bb.subgroupOf W).map φ⁆ := by
            rw [← Subgroup.map_commutator, hcomm']
        _ ≤ ⁅inSubgroup (aschbacherSolvableCore 3)
              (Subgroup.centralizer ({φ b'} : Set (autIn W K₁))), B₃⁆ :=
            Subgroup.commutator_mono hVle hB₃.symm.le
        _ ≤ thetaJ 3 B₃ := le_iSup₂_of_le (φ b') hβB (le_iSup_of_le hβ1 le_rfl)
    intro hbot
    apply hVne
    rw [eq_bot_iff, ← hbot, thetaAlpha]
    exact hJle.trans le_sup_left
  ·
    have hTne : (T.subgroupOf W).map φ ≠ ⊥ := by
      intro hbot
      apply hTK
      intro t ht
      have hmem : φ ⟨t, hTW ht⟩ ∈ (T.subgroupOf W).map φ :=
        Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr ht)
      rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, hφker] at hmem
      exact hmem
    have hTle : (T.subgroupOf W).map φ ≤ thetaT 3 B₃ := by
      refine le_iInf fun β => le_iInf fun hβ => le_iInf fun hβ1 => ?_
      rw [hB₃] at hβ
      obtain ⟨b', hb', rfl⟩ := hβ
      have hb'B : (b' : X) ∈ Bb := Subgroup.mem_subgroupOf.mp hb'
      have hb'1 : (b' : X) ≠ 1 := fun h => hβ1 (by rw [show b' = 1 from Subtype.ext h, map_one])
      exact hGL T hTW b' hb'B hb'1 (hTR _ hb'B hb'1) fun s hs K hK hne =>
        (hNF K hK hne b₀ hb₀ hb₀1').2 hs
    intro hbot
    apply hTne
    rw [eq_bot_iff, ← hbot, thetaAlpha]
    exact hTle.trans le_sup_right

end Transfer

section Lift

variable {G : Type} [Group G] [Finite G]

theorem thetaAlpha_subgroupOf_map_ne_bot_iff' {M M' : Type*} [Group M] [Group M'] [Finite M]
    (Ψ : M ≃* M') (X Y : Subgroup M) :
    thetaAlpha 3 ((X.map Ψ.toMonoidHom).subgroupOf (Y.map Ψ.toMonoidHom)) ≠ ⊥ ↔
      thetaAlpha 3 (X.subgroupOf Y) ≠ ⊥ := by
  have : Finite M' := Finite.of_equiv M Ψ.toEquiv
  let e := Y.equivMapOfInjective Ψ.toMonoidHom Ψ.injective
  have he : (X.subgroupOf Y).map e.toMonoidHom =
      (X.map Ψ.toMonoidHom).subgroupOf (Y.map Ψ.toMonoidHom) := by
    ext z
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
    · intro hz
      obtain ⟨y, rfl⟩ := e.surjective z
      refine ⟨y, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
      obtain ⟨x, hx, hxy⟩ := hz
      have : x = y := Ψ.injective hxy
      exact this ▸ hx
  rw [← he, ← thetaAlpha_map_equiv Nat.prime_three, Ne, Ne,
    Subgroup.map_eq_bot_iff_of_injective _ e.injective]

theorem mem_map_of_maximal {A : Subgroup G}
    (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (N : Subgroup G) [N.Normal] (hN3 : ¬ 3 ∣ Nat.card N) {u : G ⧸ N} (hu : u ^ 3 = 1)
    (huC : u ∈ Subgroup.centralizer ((A.map (QuotientGroup.mk' N) : Subgroup _) : Set _)) :
    u ∈ A.map (QuotientGroup.mk' N) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := hmax.1
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  have hAbc : ∀ x ∈ A.map (QuotientGroup.mk' N), ∀ y ∈ A.map (QuotientGroup.mk' N),
      x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  have hAb3 : ∀ x ∈ A.map (QuotientGroup.mk' N), x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hAe.2 x hx, map_one]
  have hzN : Subgroup.zpowers u ≤ Subgroup.normalizer ((A.map (QuotientGroup.mk' N) :
      Subgroup _) : Set _) :=
    (Subgroup.zpowers_le.mpr huC).trans (Subgroup.centralizer_le_normalizer _)
  have hEmem : ∀ x ∈ A.map (QuotientGroup.mk' N) ⊔ Subgroup.zpowers u,
      ∃ a ∈ A.map (QuotientGroup.mk' N), ∃ k : ℤ, x = a * u ^ k := by
    intro x hx
    have hx' : x ∈ ((A.map (QuotientGroup.mk' N) ⊔ Subgroup.zpowers u : Subgroup _) :
        Set _) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hzN] at hx'
    obtain ⟨a, ha, z, hz, rfl⟩ := hx'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ⟨a, ha, k, rfl⟩
  have hau : ∀ a ∈ A.map (QuotientGroup.mk' N), ∀ k : ℤ, a * u ^ k = u ^ k * a := by
    intro a ha k
    have hc : Commute a u := Subgroup.mem_centralizer_iff.mp huC a ha
    exact (hc.zpow_right k).eq
  set E := A.map (QuotientGroup.mk' N) ⊔ Subgroup.zpowers u with hE
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, k, rfl⟩ := hEmem x hx
    obtain ⟨b, hb, l, rfl⟩ := hEmem y hy
    calc a * u ^ k * (b * u ^ l) = a * (u ^ k * b) * u ^ l := by group
      _ = a * (b * u ^ k) * u ^ l := by rw [hau b hb k]
      _ = (a * b) * (u ^ k * u ^ l) := by group
      _ = (b * a) * (u ^ l * u ^ k) := by rw [hAbc a ha b hb, ← zpow_add, ← zpow_add, add_comm]
      _ = b * (a * u ^ l) * u ^ k := by group
      _ = b * (u ^ l * a) * u ^ k := by rw [hau a ha l]
      _ = b * u ^ l * (a * u ^ k) := by group
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨a, ha, k, rfl⟩ := hEmem x hx
    have hc : Commute a (u ^ k) := hau a ha k
    have huk : (u ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
    rw [hc.mul_pow, hAb3 a ha, one_mul, huk]
  set M := E.comap (QuotientGroup.mk' N) with hM
  have hAM : A ≤ M := fun x hx => Subgroup.mem_comap.mpr (Subgroup.mem_sup_left ⟨x, hx, rfl⟩)
  obtain ⟨S, hAS⟩ := (hAp.comap_subtype (K := M)).exists_le_sylow
  let f : M →* E :=
    { toFun := fun x => ⟨QuotientGroup.mk' N (x : G), Subgroup.mem_comap.mp x.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ (x : G) y) }
  have hf : Function.Surjective f := by
    rintro ⟨e, he⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N e
    exact ⟨⟨g, Subgroup.mem_comap.mpr he⟩, rfl⟩
  have hEp : IsPGroup 3 (⊤ : Subgroup E) := fun x => ⟨1, by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hE3 _ (x : E).2⟩
  have hStop : ((S.mapSurjective hf : Sylow 3 E) : Subgroup E) = ⊤ :=
    ((S.mapSurjective hf).is_maximal' hEp le_top).symm
  set S' : Subgroup G := (S : Subgroup M).map M.subtype with hS'
  have hS'p : IsPGroup 3 S' := S.isPGroup'.map M.subtype
  have hinj : Set.InjOn (QuotientGroup.mk' N) (S' : Set G) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS'p
    have hdisj : Disjoint S' N := Subgroup.disjoint_of_coprime_natCard (by
      rw [hk]
      exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN3))
    intro x hx y hy hxy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxy
    have hmem : x⁻¹ * y ∈ S' ⊓ N := ⟨S'.mul_mem (S'.inv_mem hx) hy, hxy⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
    exact eq_of_inv_mul_eq_one hmem
  have hS'E : ∀ s ∈ S', QuotientGroup.mk' N s ∈ E := by
    rintro _ ⟨s, -, rfl⟩
    exact Subgroup.mem_comap.mp s.2
  have hS'e : CFSG.Assembly.IsElemAbelian 3 S' := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hinj (S'.mul_mem x.2 y.2) (S'.mul_mem y.2 x.2) ?_)⟩⟩,
      fun x hx => hinj (S'.pow_mem hx 3) S'.one_mem ?_⟩
    · simp only [Subgroup.coe_mul, map_mul]
      exact hEc _ (hS'E _ x.2) _ (hS'E _ y.2)
    · rw [map_pow, map_one]
      exact hE3 _ (hS'E x hx)
  have hAS' : A ≤ S' := fun x hx => ⟨⟨x, hAM hx⟩, hAS hx, rfl⟩
  have hS'A : S' ≤ A := hmax.2 hS'e hAS'
  have huE : (⟨u, Subgroup.mem_sup_right (Subgroup.mem_zpowers u)⟩ : E) ∈
      ((S.mapSurjective hf : Sylow 3 E) : Subgroup E) := by
    rw [hStop]
    exact Subgroup.mem_top _
  rw [Sylow.coe_mapSurjective] at huE
  obtain ⟨s, hs, hsu⟩ := huE
  refine ⟨s, hS'A ⟨s, hs, rfl⟩, ?_⟩
  have := congrArg Subtype.val hsu
  exact this

theorem congr_thetaQuotMulAut_eq {L : Subgroup G}
    (η : L ⧸ aschbacherSolvableCore 3 L ≃*
      L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)))
    (hη : ∀ l : L, (η (l : L ⧸ aschbacherSolvableCore 3 L) : G ⧸ aschbacherSolvableCore 3 G) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 G) (l : G))
    {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hg' : QuotientGroup.mk' (aschbacherSolvableCore 3 G) g ∈ Subgroup.normalizer
      ((L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) : Subgroup _) : Set _)) :
    MulAut.congr η (thetaQuotMulAut L (L.normalizerMonoidHom ⟨g, hg⟩)) =
      (L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))).normalizerMonoidHom
        ⟨QuotientGroup.mk' (aschbacherSolvableCore 3 G) g, hg'⟩ := by
  ext k
  obtain ⟨y, rfl⟩ := η.surjective k
  induction y using QuotientGroup.induction_on with
  | H l =>
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      thetaQuotMulAut_mk, hη, normalizerMonoidHom_apply_coe, normalizerMonoidHom_apply_coe, hη,
      map_mul, map_mul, map_inv]

theorem map_autThetaQuot_eq_autIn {L : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (η : L ⧸ aschbacherSolvableCore 3 L ≃*
      L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)))
    (hη : ∀ l : L, (η (l : L ⧸ aschbacherSolvableCore 3 L) : G ⧸ aschbacherSolvableCore 3 G) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 G) (l : G)) (U : Subgroup G) :
    (autThetaQuot U L).map (MulAut.congr η).toMonoidHom =
      autIn (U.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)))
        (L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))) := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨g, hgN, hgU, rfl⟩ := mem_autThetaQuot_iff.mp hτ
    have hg' := (mem_normalizer_iff_mk_mem_normalizer Nat.prime_three hL g).mp hgN
    refine mem_autIn_iff.mpr ⟨_, hg', Subgroup.mem_map_of_mem _ hgU, ?_⟩
    exact (congr_thetaQuotMulAut_eq η hη hgN hg').symm
  · intro hσ
    obtain ⟨x, hxN, ⟨g, hgU, rfl⟩, rfl⟩ := mem_autIn_iff.mp hσ
    have hgN := (mem_normalizer_iff_mk_mem_normalizer Nat.prime_three hL g).mpr hxN
    exact ⟨_, mem_autThetaQuot_iff.mpr ⟨g, hgN, hgU, rfl⟩, congr_thetaQuotMulAut_eq η hη hgN hxN⟩

noncomputable def comapQuotientEquiv (N : Subgroup G) [N.Normal] (K : Subgroup (G ⧸ N)) :
    K.comap (QuotientGroup.mk' N) ⧸ N.subgroupOf (K.comap (QuotientGroup.mk' N)) ≃* K :=
  let φ : K.comap (QuotientGroup.mk' N) →* K :=
    { toFun := fun h => ⟨QuotientGroup.mk' N h, h.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ (x : G) y) }
  have hφ : Function.Surjective φ := by
    rintro ⟨k, hk⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N k
    exact ⟨⟨g, hk⟩, rfl⟩
  have hker : N.subgroupOf (K.comap (QuotientGroup.mk' N)) = φ.ker := by
    ext h
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hh
      exact Subtype.ext ((QuotientGroup.eq_one_iff (h : G)).mpr hh)
    · intro hh
      exact (QuotientGroup.eq_one_iff (h : G)).mp (congrArg Subtype.val hh)
  (QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

end Lift

section RankComponent

variable {X : Type} [Group X] [Finite X]

theorem pRank_top_le_localRank_of_le_centralizer {K L : Subgroup X}
    (hL : CFSG.IsQuasisimple L) (hKL : K ≤ Subgroup.centralizer (L : Set X)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ CFSG.Assembly.RankThreeEven.localRank 3 X := by
  have h2 : 2 ∣ Nat.card L := by
    by_contra h
    have hodd : Odd (Nat.card L) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
    have := CFSG.LocalCores.isQuasisimple_nontrivial hL
    have : Group.IsPerfect L := hL.1
    exact Group.IsPerfect.not_isSolvable L (CFSG.FeitThompson.isSolvable_of_odd_natCard L hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 h2
  have ht' : orderOf (t : X) = 2 := by rw [Subgroup.orderOf_coe, ht]
  have hT1 : Subgroup.zpowers (t : X) ≠ ⊥ := by
    intro h
    have hmem : (t : X) ∈ Subgroup.zpowers (t : X) := Subgroup.mem_zpowers _
    rw [h, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at ht'
    norm_num at ht'
  have hT2 : IsPGroup 2 (Subgroup.zpowers (t : X)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one])
  have hKN : K ≤ Subgroup.normalizer ((Subgroup.zpowers (t : X) : Subgroup X) : Set X) :=
    hKL.trans ((Subgroup.centralizer_le (Subgroup.zpowers_le.mpr t.2)).trans
      (Subgroup.centralizer_le_normalizer _))
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ CFSG.Open.pRank 3 K := by
    have h := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) K.subtype K.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  have h3 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hKN
  refine h1.trans (h3.trans (le_csSup ⟨Nat.card X, ?_⟩ ⟨_, ⟨_, hT1, hT2, rfl⟩, rfl⟩))
  rintro _ ⟨Z, -, rfl⟩
  exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card 3 Nat.prime_three Z).trans
    (Subgroup.card_le_card_group Z)

end RankComponent

end Item422Proof

open Item422Proof

section Main

theorem rank3II_4_22_of_fixComm (h45 : Item4_5)
    (hKF : ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G →
      ∀ K L : Subgroup (G ⧸ aschbacherSolvableCore 3 G), IsComponent K → IsComponent L → K ≠ L →
      ∀ z ∈ Subgroup.center K, orderOf z = 3 → ∀ σ τ : MulAut K, σ z = z → τ z = z →
        σ * τ * σ⁻¹ * τ⁻¹ ∈ (MulAut.conj : K →* MulAut K).range) : Item4_22 := by
  intro G _ _ hS4 A hmax h27 c hcA hcZ hc1
  have hZn : (Subgroup.zpowers c).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcZ)
  by_cases h1 : thetaAlpha 3 (A.map (QuotientGroup.mk' (Subgroup.zpowers c))) ≤
      aschbacherSolvableCore 3 (G ⧸ Subgroup.zpowers c)
  · exact Or.inl h1
  right
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hmax.1
  have hAE : IsElementaryAbelian 3 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).mpr hAe
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  have hAcard : Nat.card A = 3 ^ 3 := by rw [h27]; norm_num
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hAe.2 c hcA) hc1
  have hZA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
  have hZc : Subgroup.zpowers c ≤ Subgroup.center G := Subgroup.zpowers_le.mpr hcZ
  have hZp : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hc3]
  have hnorm : ∀ L ∈ thetaComponents 3 G, A ≤ Subgroup.normalizer (L : Set G) := fun L hL =>
    h45 G hS4 A hAp (Or.inr ⟨hAe, 3, le_rfl, by rw [h27]; norm_num⟩) L hL
  obtain ⟨C', hC'⟩ := IsElementaryAbelian.exists_isCompl 3 A ((Subgroup.zpowers c).subgroupOf A)
  set B := C'.map A.subtype with hB
  have hBA : B ≤ A := Subgroup.map_subtype_le _
  have hBZ : Disjoint B (Subgroup.zpowers c) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro _ ⟨⟨y, hy, rfl⟩, hxZ⟩
    have hyZ : y ∈ (Subgroup.zpowers c).subgroupOf A := Subgroup.mem_subgroupOf.mpr hxZ
    have hmem : y ∈ (Subgroup.zpowers c).subgroupOf A ⊓ C' := ⟨hyZ, hy⟩
    rw [hC'.inf_eq_bot, Subgroup.mem_bot] at hmem
    rw [hmem, map_one]
    exact Subgroup.one_mem _
  have hBZA : B ⊔ Subgroup.zpowers c = A := by
    have h := congrArg (Subgroup.map A.subtype) hC'.sup_eq_top
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZA,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    rw [sup_comm]
    exact h
  obtain ⟨L, hL, a, ha, hker, -, hcard, hQK⟩ := central_line_faithful_component_detection
    Nat.prime_three hAE hAcard (Subgroup.zpowers c) hZA hZc hZp hnorm h1 B hBA hBZ hBZA
  obtain ⟨-, hBb, -, hBbcard, hQmap, -, hθX, hAK⟩ := central_line_setup Nat.prime_three hAE
    hAcard (Subgroup.zpowers c) hZc hZp hnorm h1 B hBA hBZ hBZA
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hAp
  have haT : ∀ (x : A) (hxN : (x : G) ∈ Subgroup.normalizer (L : Set G)),
      a x = thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) := by
    intro x hxN
    ext y
    induction y using QuotientGroup.induction_on with
    | H l =>
      rw [ha x l (L.normalizerMonoidHom ⟨x, hxN⟩ l) (normalizerMonoidHom_apply_coe hxN l),
        thetaQuotMulAut_mk]
  have hAut : autThetaQuot A L = a.range := by
    ext σ
    rw [mem_autThetaQuot_iff, MonoidHom.mem_range]
    constructor
    · rintro ⟨h, hN, hA, rfl⟩
      exact ⟨⟨h, hA⟩, haT ⟨h, hA⟩ hN⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, hnorm L hL x.2, x.2, (haT x (hnorm L hL x.2)).symm⟩
  refine ⟨L, hL, by rw [hAut, hcard]; norm_num, ?_⟩
  obtain ⟨η, a', -, hη, ha', -, -, hkerC, -, -⟩ :=
    theta_component_quotient_action Nat.prime_three hL A (hnorm L hL)
  have haa' : ∀ x : A, a x = a' x := by
    intro x
    ext y
    induction y using QuotientGroup.induction_on with
    | H l =>
      have hxl : (x : G) * l * (x : G)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hnorm L hL x.2) l).mp l.2
      rw [ha x l ⟨_, hxl⟩ rfl, ha' x l ⟨_, hxl⟩ rfl]
  have hfaith : ∀ x ∈ A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)),
      x ∈ Subgroup.centralizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) :
        Subgroup _) : Set _) ↔
        x ∈ Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 G) c) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hkerC ⟨x, hx⟩, ← haa', hker]
    constructor
    · intro hxZ
      rw [← MonoidHom.map_zpowers]
      exact Subgroup.mem_map_of_mem _ hxZ
    · intro hxz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
      have hck : c ^ k = x := hinj (A.zpow_mem hcA k) hx (by rw [map_zpow, hk])
      subst hck
      exact Subgroup.zpow_mem_zpowers c k
  have hKX : CFSG.IsKGroup (G ⧸ aschbacherSolvableCore 3 G) := theta_quotient_isKGroup hS4.kGroup
  have hcbZ : QuotientGroup.mk' (aschbacherSolvableCore 3 G) c ∈
      Subgroup.center (G ⧸ aschbacherSolvableCore 3 G) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _) (Subgroup.mem_map_of_mem _ hcZ)
  have hcb3 : orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 G) c) = 3 := by
    refine orderOf_eq_prime (by rw [← map_pow, hAe.2 c hcA, map_one]) fun h => hc1 ?_
    exact hinj hcA A.one_mem (by rw [h, map_one])
  have hBcard9 : Nat.card (B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))) = 9 := by
    rw [hBbcard]; norm_num
  have hBZX : B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ⊓
      Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 G) c) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨b, hb, rfl⟩, hbz⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbz
    have hbc : c ^ k = b := hinj (A.zpow_mem hcA k) (hBA hb) (by rw [map_zpow, hk])
    have hbZ : b ∈ B ⊓ Subgroup.zpowers c := ⟨hb, hbc ▸ Subgroup.zpow_mem_zpowers c k⟩
    rw [disjoint_iff.mp hBZ, Subgroup.mem_bot] at hbZ
    rw [hbZ, map_one]
    exact Subgroup.one_mem _
  have hABZX : A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) =
      B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ⊔
        Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 G) c) := by
    rw [← hBZA, Subgroup.map_sup, MonoidHom.map_zpowers]
  have hQ : ¬ thetaAlpha 3 (B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))) ≤
      Subgroup.centralizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) :
        Subgroup _) : Set _) := by
    rw [← hQmap]
    exact hQK
  have hX := thetaAlpha_autIn_ne_bot_of_fixComm (hKF G hS4) KFacts.kpSz hθX hKX hcbZ hcb3 hBb
    hBcard9 hBZX hABZX (fun u hu huC => mem_map_of_maximal hmax _
      three_not_dvd_card_aschbacherSolvableCore hu huC) hAK
    (isComponent_map_of_mem_thetaComponents Nat.prime_three hL) hfaith hQ
  rw [← thetaAlpha_subgroupOf_map_ne_bot_iff' (MulAut.congr η), map_autThetaQuot_eq_autIn hL η hη,
    map_autThetaQuot_eq_autIn hL η hη, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective _)]
  exact hX

end Main

end CFSG.RankThree.PartTwo.Sec4
