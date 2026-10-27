module

public import CFSG.RankThree.PartOne.KF.CentralQuot
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
public import CFSG.RankThree.PartOne.S12.Sec12Fus
public import CFSG.RankThree.PartOne.KF.LayerGen

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG CFSG.LocalCores CFSG.RankThree.GroupTheory.SteinbergBY

variable {E M P : Type} [Group E] [Group M] [Group P] {p : ℕ}

theorem map_inSubgroup_perfectResidual [Finite E] [Finite P] (f : E →* P) (Y : Subgroup E) :
    (inSubgroup perfectResidual Y).map f = inSubgroup perfectResidual (Y.map f) := by
  have h := (perfect_residual_transport (f.comp Y.subtype)).1
  have hr : (f.comp Y.subtype).range = Y.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  unfold inSubgroup
  rw [Subgroup.map_map, h]
  exact congrArg (fun H : Subgroup P => (perfectResidual ↥H).map H.subtype) hr

theorem not_le_center_of_isQuasisimple' {Γ : Type*} [Group Γ] {Q : Subgroup Γ}
    (hQ : IsQuasisimple ↥Q) : ¬ Q ≤ Subgroup.center Γ := by
  intro hle
  have hperf := hQ.1
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have hcomm : commutator ↥Q = ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _ b _
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hle a.2) b)
  have : (⊤ : Subgroup ↥Q) = ⊥ := by
    rw [← hperf.commutator_eq_top, hcomm]
  exact (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup ↥Q)).mp inferInstance this

namespace IsCentralPQuot

variable {ε : E →* P} (h : IsCentralPQuot p ε)

include h in
theorem mem_centralizer_iff_map {b : E} (hb : b ^ p = 1) {x : E} :
    x ∈ Subgroup.centralizer ({b} : Set E) ↔ ε x ∈ Subgroup.centralizer ({ε b} : Set P) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    rw [← map_mul, ← map_mul, hx]
  · intro hx
    exact (h.commute_of_map_commute hb (show Commute (ε b) (ε x) from hx.symm)).eq.symm

include h in
theorem map_centralizer {b : E} (hb : b ^ p = 1) :
    (Subgroup.centralizer ({b} : Set E)).map ε = Subgroup.centralizer ({ε b} : Set P) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h.mem_centralizer_iff_map hb).1 hx
  · intro hy
    obtain ⟨x, rfl⟩ := h.surjective y
    exact ⟨x, (h.mem_centralizer_iff_map hb).2 hy, rfl⟩

include h in
theorem exists_lift_mem {K : Subgroup E} {x : P} (hxK : x ∈ K.map ε) (hx : x ^ p = 1) :
    ∃ y ∈ K, ε y = x ∧ y ^ p = 1 := by
  obtain ⟨y₀, hy₀K, hy₀⟩ := hxK
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder h.coprime 1 0
  refine ⟨y₀ ^ c, K.pow_mem hy₀K c, ?_, ?_⟩
  · rw [map_pow, hy₀, pow_eq_pow_mod c hx, hc1]
    exact (pow_eq_pow_mod 1 hx).symm.trans (pow_one x)
  · have hmem : y₀ ^ p ∈ ε.ker := by
      rw [MonoidHom.mem_ker, map_pow, hy₀, hx]
    have hk : (y₀ ^ p) ^ Nat.card ε.ker = 1 := by
      have := pow_card_eq_one' (G := ε.ker) (x := ⟨y₀ ^ p, hmem⟩)
      simpa using congrArg Subtype.val this
    have hkc : Nat.card ε.ker ∣ c := (Nat.modEq_zero_iff_dvd).mp hc2
    obtain ⟨t, ht⟩ := hkc
    calc (y₀ ^ c) ^ p = (y₀ ^ p) ^ c := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((y₀ ^ p) ^ Nat.card ε.ker) ^ t := by rw [ht, pow_mul]
      _ = 1 := by rw [hk, one_pow]

include h in
theorem comp_mulEquiv {E' : Type*} [Group E'] (e : E' ≃* E) :
    IsCentralPQuot p (ε.comp e.toMonoidHom) where
  surjective := h.surjective.comp e.surjective
  central := by
    intro x hx
    have hc := h.central (show e x ∈ ε.ker from hx)
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul]
    exact hc (e g)
  coprime := by
    have hker : (ε.comp e.toMonoidHom).ker = ε.ker.comap e.toMonoidHom := rfl
    have h2 : Nat.card ↥(ε.ker.comap e.toMonoidHom) = Nat.card ↥ε.ker := by
      rw [show ε.ker.comap e.toMonoidHom = ε.ker.map (e.symm : E →* E') from
        Subgroup.comap_equiv_eq_map_symm e ε.ker]
      exact Subgroup.card_map_of_injective e.symm.injective
    rw [hker, h2]
    exact h.coprime

end IsCentralPQuot

theorem map_center_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := e.surjective g
    show e a * e x = e x * e a
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx a]
  · intro hy
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨x, ?_, rfl⟩
    show x ∈ Subgroup.center A
    rw [Subgroup.mem_center_iff]
    intro a
    apply e.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hy (e a)

theorem exists_centerQuotient_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nonempty (A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B) :=
  ⟨QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (map_center_mulEquiv e)⟩

theorem card_center_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (Subgroup.center A) = Nat.card (Subgroup.center B) := by
  rw [← map_center_mulEquiv e, Subgroup.card_map_of_injective e.injective]

theorem centerQuotientEquiv_of_surjective {P Q : Type*} [Group P] [Group Q]
    (hP : Group.IsPerfect P) (f : P →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center P) :
    Nonempty (P ⧸ Subgroup.center P ≃* Q ⧸ Subgroup.center Q) := by
  have hc : Subgroup.center P = ((QuotientGroup.mk' (Subgroup.center Q)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      comap_center_eq_of_perfect hP f hf hker]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))⟩

section Cover

variable [Finite E] [Finite M] [Finite P] {ε : E →* P} {q : M →* P}
  (hε : IsCentralPQuot p ε) (hq : IsCentralPQuot p q) {b : E} {bM : M} (hb : b ^ p = 1)
  (hbM : bM ^ p = 1) (hbb : ε b = q bM)

include hε hq hb hbM hbb in
theorem map_perfectResidual_centralizer :
    (inSubgroup perfectResidual (Subgroup.centralizer ({b} : Set E))).map ε =
      (inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M))).map q := by
  rw [map_inSubgroup_perfectResidual, map_inSubgroup_perfectResidual, hε.map_centralizer hb,
    hq.map_centralizer hbM, hbb]

theorem isPerfect_inSubgroup_perfectResidual (Y : Subgroup E) :
    Group.IsPerfect ↥(inSubgroup perfectResidual Y) := by
  have := (perfect_residual_characterization (G := ↥Y)).2.2.1
  exact Group.IsPerfect.map Y.subtype

omit [Finite E] [Finite P] in
theorem ker_subgroupMap_le_center (hε : IsCentralPQuot p ε) (K : Subgroup E) :
    (ε.subgroupMap K).ker ≤ Subgroup.center ↥K := by
  intro x hx
  have hx1 : ε (x : E) = 1 := by
    have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    simpa using this
  have hxc : (x : E) ∈ Subgroup.center E := hε.central (MonoidHom.mem_ker.2 hx1)
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.1 hxc g)

include hε hq hb hbM hbb in
theorem isQuasisimple_perfectResidual_centralizer
    (h : IsQuasisimple ↥(inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M)))) :
    IsQuasisimple ↥(inSubgroup perfectResidual (Subgroup.centralizer ({b} : Set E))) := by
  set KE := inSubgroup perfectResidual (Subgroup.centralizer ({b} : Set E)) with hKE
  set KM := inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M)) with hKM
  have hmap : KE.map ε = KM.map q := map_perfectResidual_centralizer hε hq hb hbM hbb
  have hKMnc : ¬ KM ≤ q.ker := fun hle =>
    not_le_center_of_isQuasisimple' h (fun x hx => hq.central (hle hx))
  have hbar : IsQuasisimple ↥(KE.map ε) := hmap ▸ isQuasisimple_map h q hKMnc
  exact (isQuasisimple_iff_of_surjective (isPerfect_inSubgroup_perfectResidual _)
    (ε.subgroupMap KE) (ε.subgroupMap_surjective KE) (ker_subgroupMap_le_center hε KE)).mpr hbar

include hε hq hb hbM hbb in
theorem not_dvd_card_center_perfectResidual_centralizer (hp : p.Prime)
    (hz : ¬ p ∣ Nat.card (Subgroup.center
      ↥(inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M))))) :
    ¬ p ∣ Nat.card (Subgroup.center
      ↥(inSubgroup perfectResidual (Subgroup.centralizer ({b} : Set E)))) := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  set KE := inSubgroup perfectResidual (Subgroup.centralizer ({b} : Set E)) with hKE
  set KM := inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M)) with hKM
  have hmap : KE.map ε = KM.map q := map_perfectResidual_centralizer hε hq hb hbM hbb
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzp : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hzord
    exact hp.one_lt.ne hzord
  set x : E := (((z : ↥(Subgroup.center ↥KE)) : ↥KE) : E) with hx
  have hxK : x ∈ KE := ((z : ↥(Subgroup.center ↥KE)) : ↥KE).2
  have hxp : x ^ p = 1 := by
    have := congrArg (fun w : ↥(Subgroup.center ↥KE) => ((w : ↥KE) : E)) hzp
    simpa using this
  have hεx : ε x ∈ KM.map q := hmap ▸ ⟨x, hxK, rfl⟩
  have hεxp : (ε x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
  obtain ⟨y, hyK, hyq, hyp⟩ := hq.exists_lift_mem hεx hεxp
  have hycen : (⟨y, hyK⟩ : ↥KM) ∈ Subgroup.center ↥KM := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have hk : q (k : M) ∈ KE.map ε := hmap ▸ ⟨(k : M), k.2, rfl⟩
    obtain ⟨k', hk'K, hk'⟩ := hk
    have hzc := Subgroup.mem_center_iff.1 z.2 ⟨k', hk'K⟩
    have h2 : ε k' * ε x = ε x * ε k' := by
      have := congrArg (fun w : ↥KE => ε (w : E)) hzc
      simpa [map_mul] using this
    have hcomm : Commute (q y) (q (k : M)) := by
      rw [hyq, ← hk']
      exact h2.symm
    exact (hq.commute_of_map_commute hyp hcomm).eq.symm
  have hy1 : y = 1 := by
    by_contra hne
    have hordc : orderOf (⟨⟨y, hyK⟩, hycen⟩ : ↥(Subgroup.center ↥KM)) = p := by
      rw [← Subgroup.orderOf_coe (⟨⟨y, hyK⟩, hycen⟩ : ↥(Subgroup.center ↥KM))]
      show orderOf (⟨y, hyK⟩ : ↥KM) = p
      rw [← Subgroup.orderOf_coe (⟨y, hyK⟩ : ↥KM)]
      exact orderOf_eq_prime hyp hne
    have hcen : orderOf (⟨⟨y, hyK⟩, hycen⟩ : ↥(Subgroup.center ↥KM)) ∣
        Nat.card ↥(Subgroup.center ↥KM) := orderOf_dvd_natCard _
    rw [hordc] at hcen
    exact hz hcen
  have hεx1 : ε x = 1 := by rw [← hyq, hy1, map_one]
  have hx1 : x = 1 := hε.eq_one_of_pow_eq_one (MonoidHom.mem_ker.2 hεx1) hxp
  exact hz1 (Subtype.ext (Subtype.ext hx1))

include hε hq hb hbM hbb in
theorem exists_centerQuotientEquiv_perfectResidual_centralizer :
    Nonempty (↥(inSubgroup perfectResidual (Subgroup.centralizer ({b} : Set E))) ⧸
        Subgroup.center ↥(inSubgroup perfectResidual (Subgroup.centralizer ({b} : Set E))) ≃*
      ↥(inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M))) ⧸
        Subgroup.center ↥(inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M)))) := by
  set KE := inSubgroup perfectResidual (Subgroup.centralizer ({b} : Set E)) with hKE
  set KM := inSubgroup perfectResidual (Subgroup.centralizer ({bM} : Set M)) with hKM
  have hmap : KE.map ε = KM.map q := map_perfectResidual_centralizer hε hq hb hbM hbb
  obtain ⟨e₁⟩ := centerQuotientEquiv_of_surjective (isPerfect_inSubgroup_perfectResidual _)
    (ε.subgroupMap KE) (ε.subgroupMap_surjective KE) (ker_subgroupMap_le_center hε KE)
  obtain ⟨e₂⟩ := centerQuotientEquiv_of_surjective (isPerfect_inSubgroup_perfectResidual _)
    (q.subgroupMap KM) (q.subgroupMap_surjective KM) (ker_subgroupMap_le_center hq KM)
  obtain ⟨e₃⟩ := exists_centerQuotient_mulEquiv (MulEquiv.subgroupCongr hmap)
  exact ⟨e₁.trans (e₃.trans e₂.symm)⟩

end Cover

theorem inSubgroup_perfectResidual_eq_of_ker {G : Type} [Group G] [Finite G] {C B : Subgroup G}
    (hBC : B ≤ C) (hB : Group.IsPerfect ↥B) {Q : Type*} [Group Q] [Group.IsSolvable Q]
    (Φ : ↥C →* Q) (hker : Φ.ker = B.subgroupOf C) :
    inSubgroup perfectResidual C = B := by
  have : (B.subgroupOf C).Normal := hker ▸ MonoidHom.normal_ker _
  have hsolv : Group.IsSolvable (↥C ⧸ B.subgroupOf C) := by
    have h1 : Group.IsSolvable (↥C ⧸ Φ.ker) :=
      Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective Φ)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (QuotientGroup.quotientMulEquivOfEq hker.symm).toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq hker.symm).injective
  apply le_antisymm
  · have h1 := ((perfect_residual_characterization (G := ↥C)).2.2.2.2.1
      (B.subgroupOf C)).1 hsolv
    calc inSubgroup perfectResidual C = (perfectResidual ↥C).map C.subtype := rfl
      _ ≤ (B.subgroupOf C).map C.subtype := Subgroup.map_mono h1
      _ = B := Subgroup.map_subgroupOf_eq_of_le hBC
  · have hperf : Group.IsPerfect ↥(B.subgroupOf C) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hBC).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hBC).symm.surjective
    have h2 := (perfect_residual_transport (MonoidHom.id ↥C)).2.2 _ hperf
    calc B = (B.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hBC).symm
      _ ≤ (perfectResidual ↥C).map C.subtype := Subgroup.map_mono h2

section Count

variable [Finite E] [Finite M] [Finite P] {ε : E →* P} {q : M →* P}

omit [Finite E] [Finite P] in
theorem card_inf_eq_card_map_inf (hε : IsCentralPQuot p ε) {A₀ K : Subgroup E}
    (hA : ∀ a ∈ A₀, a ^ p = 1) :
    Nat.card ↥(A₀ ⊓ K) = Nat.card ↥(A₀.map ε ⊓ K.map ε) := by
  have hmap : (A₀ ⊓ K).map ε = A₀.map ε ⊓ K.map ε := by
    apply le_antisymm (Subgroup.map_inf_le _ _ _)
    rintro y ⟨⟨a, haA, rfl⟩, hyK⟩
    have hap : (ε a) ^ p = 1 := by rw [← map_pow, hA a haA, map_one]
    obtain ⟨k, hkK, hk, hkp⟩ := hε.exists_lift_mem hyK hap
    have hak : a = k := hε.eq_of_map_eq (hA a haA) hkp hk.symm
    exact ⟨a, ⟨haA, hak ▸ hkK⟩, rfl⟩
  have hinj : Function.Injective (ε.subgroupMap (A₀ ⊓ K)) := by
    intro x y hxy
    have h1 : ε (x : E) = ε (y : E) := congrArg Subtype.val hxy
    exact Subtype.ext (hε.eq_of_map_eq (hA _ x.2.1) (hA _ y.2.1) h1)
  have hbij : Function.Bijective (ε.subgroupMap (A₀ ⊓ K)) :=
    ⟨hinj, ε.subgroupMap_surjective _⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), hmap]

theorem mem_normalizer_of_conj_mem {Γ : Type*} [Group Γ] {S : Subgroup Γ} {a : Γ}
    (h1 : ∀ x ∈ S, a * x * a⁻¹ ∈ S) (h2 : ∀ x ∈ S, a⁻¹ * x * a ∈ S) :
    a ∈ Subgroup.normalizer (S : Set Γ) :=
  Subgroup.mem_normalizer_iff.mpr fun x => ⟨h1 x, fun hx => by simpa [mul_assoc] using h2 _ hx⟩

omit [Finite M] in
theorem exists_invariant_two_subgroup (hε : IsCentralPQuot p ε) (hq : IsCentralPQuot p q)
    {A₀ KE : Subgroup E} {T₀ U KM : Subgroup M}
    (hmap : KE.map ε = KM.map q) (hAT : A₀.map ε = T₀.map q)
    (hAK : A₀ ≤ Subgroup.normalizer (KE : Set E)) (hU : U ≤ KM) (hU2 : IsPGroup 2 U)
    (hTU : T₀ ≤ Subgroup.normalizer (U : Set M)) (hT : ∀ t ∈ T₀, t ^ p = 1)
    (hnc : ∃ u ∈ U, ∃ t ∈ T₀, u * t ≠ t * u) :
    ∃ S : Subgroup E, S ≤ KE ∧ IsPGroup 2 S ∧ A₀ ≤ Subgroup.normalizer (S : Set E) ∧
      ∃ x ∈ S, ∃ a ∈ A₀, x * a ≠ a * x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ubar : Subgroup P := U.map q with hUbar
  set W : Subgroup E := KE ⊓ Ubar.comap ε with hW
  have hAW : ∀ a ∈ A₀, ∀ w ∈ W, a * w * a⁻¹ ∈ W := by
    intro a ha w hw
    have haN := Subgroup.mem_normalizer_iff.1 (hAK ha) w
    refine ⟨haN.1 hw.1, ?_⟩
    obtain ⟨t, htT, hta⟩ : ε a ∈ T₀.map q := hAT ▸ ⟨a, ha, rfl⟩
    have hwU : ε w ∈ Ubar := hw.2
    obtain ⟨u, huU, hu⟩ := hwU
    have htn := Subgroup.mem_normalizer_iff.1 (hTU htT) u
    have : ε (a * w * a⁻¹) = q (t * u * t⁻¹) := by
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, ← hta, hu]
    show ε (a * w * a⁻¹) ∈ Ubar
    rw [this]
    exact ⟨_, htn.1 huU, rfl⟩
  have hAWn : ∀ a ∈ A₀, a ∈ Subgroup.normalizer (W : Set E) := fun a ha =>
    mem_normalizer_of_conj_mem (hAW a ha) (fun w hw => by
      have := hAW a⁻¹ (A₀.inv_mem ha) w hw
      simpa using this)
  let fW : ↥W →* ↥Ubar := (ε.comp W.subtype).codRestrict Ubar (fun w => w.2.2)
  have hfW : Function.Surjective fW := by
    rintro ⟨y, hy⟩
    have hyKM : y ∈ KM.map q := by
      obtain ⟨u, huU, rfl⟩ := hy
      exact ⟨u, hU huU, rfl⟩
    obtain ⟨k, hkK, hk⟩ : y ∈ KE.map ε := hmap ▸ hyKM
    exact ⟨⟨k, hkK, show ε k ∈ Ubar from hk ▸ hy⟩, Subtype.ext hk⟩
  have hkerW : fW.ker ≤ Subgroup.center ↥W := by
    intro x hx
    have hx1 : ε (x : E) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have hxc := hε.central (MonoidHom.mem_ker.2 hx1)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 hxc g)
  have hUbarP : IsPGroup 2 ↥Ubar :=
    hU2.of_surjective (q.subgroupMap U) (q.subgroupMap_surjective U)
  have : Group.IsNilpotent ↥Ubar := hUbarP.isNilpotent
  have : Group.IsNilpotent ↥W := Subgroup.isNilpotent_of_ker_le_center fW hkerW
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 ↥W) := inferInstance
  have hS₀c : (S₀ : Subgroup ↥W).Characteristic :=
    Sylow.characteristic_of_normal S₀ inferInstance
  set S : Subgroup E := (S₀ : Subgroup ↥W).map W.subtype with hSdef
  have hSW : S ≤ W := Subgroup.map_subtype_le _
  have key : ∀ a ∈ A₀, ∀ x ∈ S, a * x * a⁻¹ ∈ S := by
    intro a ha x hx
    obtain ⟨s₀, hs₀, rfl⟩ := hx
    let φ : MulAut ↥W := W.normalizerMonoidHom ⟨a, hAWn a ha⟩
    have h1 : φ s₀ ∈ (S₀ : Subgroup ↥W) :=
      Subgroup.characteristic_iff_map_le.1 hS₀c φ ⟨s₀, hs₀, rfl⟩
    exact ⟨φ s₀, h1, rfl⟩
  refine ⟨S, hSW.trans inf_le_left, ?_, ?_, ?_⟩
  · exact S₀.isPGroup'.of_surjective (W.subtype.subgroupMap (S₀ : Subgroup ↥W))
      (W.subtype.subgroupMap_surjective _)
  · intro a ha
    exact mem_normalizer_of_conj_mem (key a ha) (fun x hx => by
      have := key a⁻¹ (A₀.inv_mem ha) x hx
      simpa using this)
  · obtain ⟨u, huU, t, htT, hut⟩ := hnc
    obtain ⟨a, haA, hat⟩ : ∃ a ∈ A₀, ε a = q t := by
      have : q t ∈ A₀.map ε := hAT ▸ ⟨t, htT, rfl⟩
      obtain ⟨a, ha, h⟩ := this
      exact ⟨a, ha, h⟩
    have hSyl : ((Sylow.mapSurjective (f := fW) hfW S₀ : Sylow 2 ↥Ubar) : Subgroup ↥Ubar) = ⊤ :=
      ((Sylow.mapSurjective (f := fW) hfW S₀).is_maximal' (hUbarP.to_subgroup ⊤) le_top).symm
    have hqu : (⟨q u, ⟨u, huU, rfl⟩⟩ : ↥Ubar) ∈ (S₀ : Subgroup ↥W).map fW := by
      have h1 : (⟨q u, ⟨u, huU, rfl⟩⟩ : ↥Ubar) ∈
          ((Sylow.mapSurjective (f := fW) hfW S₀ : Sylow 2 ↥Ubar) : Subgroup ↥Ubar) := by
        rw [hSyl]
        exact Subgroup.mem_top _
      rwa [Sylow.coe_mapSurjective] at h1
    obtain ⟨s₀, hs₀, hs₀u⟩ := hqu
    refine ⟨(s₀ : E), ⟨s₀, hs₀, rfl⟩, a, haA, fun hcomm => hut ?_⟩
    have hεx : ε (s₀ : E) = q u := congrArg Subtype.val hs₀u
    have hcm : Commute (q t) (q u) := by
      show q t * q u = q u * q t
      rw [← hat, ← hεx, ← map_mul, ← map_mul, hcomm]
    exact (hq.commute_of_map_commute (hT t htT) hcm).eq.symm

end Count

section Ambient

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {b : G}

theorem kLayer_eq_perfectResidual
    (hq : IsQuasisimple ↥(inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({b} : Set G)))) :
    kLayer L b = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) := by
  set Mg := L ⊓ Subgroup.centralizer ({b} : Set G) with hMg
  have hqe : IsQuasisimple ↥(perfectResidual ↥Mg) := by
    have e := Subgroup.equivMapOfInjective (perfectResidual ↥Mg) Mg.subtype Mg.subtype_injective
    exact isQuasisimple_of_mulEquiv e.symm hq
  have hlayer : layer ↥Mg = perfectResidual ↥Mg :=
    layer_eq_of_normal inferInstance hqe (perfect_residual_characterization (G := ↥Mg)).2.2.2.1
  have h1 : kLayer L b = (layer ↥Mg).map Mg.subtype := rfl
  rw [h1, hlayer]
  rfl

omit [Finite G] in
theorem map_centralizer_subtype (hb : b ∈ L) :
    (Subgroup.centralizer ({(⟨b, hb⟩ : ↥L)} : Set ↥L)).map L.subtype =
      L ⊓ Subgroup.centralizer ({b} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have hy' : y * (⟨b, hb⟩ : ↥L) = ⟨b, hb⟩ * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hy')
  · rintro ⟨hxL, hxc⟩
    have hxc' : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.1 hxc
    exact ⟨⟨x, hxL⟩, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hxc'), rfl⟩

theorem kLayer_eq_map_of_isQuasisimple (hb : b ∈ L)
    (hq : IsQuasisimple ↥(inSubgroup perfectResidual
      (Subgroup.centralizer ({(⟨b, hb⟩ : ↥L)} : Set ↥L)))) :
    kLayer L b = (inSubgroup perfectResidual
      (Subgroup.centralizer ({(⟨b, hb⟩ : ↥L)} : Set ↥L))).map L.subtype ∧
      IsQuasisimple ↥(kLayer L b) := by
  set KE := inSubgroup perfectResidual (Subgroup.centralizer ({(⟨b, hb⟩ : ↥L)} : Set ↥L))
    with hKE
  have hK : KE.map L.subtype = inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({b} : Set G)) := by
    rw [hKE, map_inSubgroup_perfectResidual_of_injective L.subtype L.subtype_injective,
      map_centralizer_subtype hb]
  have hqK : IsQuasisimple ↥(KE.map L.subtype) :=
    isQuasisimple_of_mulEquiv (Subgroup.equivMapOfInjective KE L.subtype L.subtype_injective) hq
  rw [hK] at hqK
  have hk := kLayer_eq_perfectResidual hqK
  refine ⟨hk.trans hK.symm, ?_⟩
  rw [hk]
  exact hqK

end Ambient

end CFSG.RankThree.PartOne.KFU
