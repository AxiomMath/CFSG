module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CRed1
public import CFSG.RankThree.PartTwo.Sec12.Hering129HC9
import CFSG.RankThree.PartTwo.Sec12.KS128BCensus
import CFSG.RankThree.PartTwo.Sec12.Hering129Setup
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJTools
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item136E
import CFSG.RankThree.PartTwo.Sec12.Hering129HLift
public import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartTwo.Sec12.Hering129Defs
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Hering129C

section Basic

variable {G : Type} [Group G] [Finite G]

@[expose] def resI (L : Subgroup G) (b : G) : Subgroup G :=
  inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G))

theorem resI_le_inf (L : Subgroup G) (b : G) :
    resI L b ≤ L ⊓ Subgroup.centralizer ({b} : Set G) := Subgroup.map_subtype_le _

theorem resI_le_L (L : Subgroup G) (b : G) : resI L b ≤ L := (resI_le_inf L b).trans inf_le_left

theorem isPerfect_resI (L : Subgroup G) (b : G) : Group.IsPerfect (resI L b) :=
  Sec6.isPerfect_inSubgroup_perfectResidual _

theorem le_normalizer_resI (L : Subgroup G) (b : G) :
    L ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (resI L b : Set G) :=
  CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _
    |> fun h => Subgroup.le_normalizer.trans h

variable {A L K S : Subgroup G} {c b a : G}

theorem c_mem_resI (cfg : Cfg129 G A c L b a K S) : c ∈ resI L b := by
  obtain ⟨hbA, -⟩ := cfg.point_facts
  exact BCensus.inf_le_residual cfg.std hbA cfg.hb.2 ⟨cfg.std.mem_A, cfg.std.mem_L⟩

theorem a_mem_resI (cfg : Cfg129 G A c L b a K S) : a ∈ resI L b := by
  obtain ⟨hbA, -⟩ := cfg.point_facts
  exact BCensus.inf_le_residual cfg.std hbA cfg.hb.2 cfg.ha

theorem hIK_cfg (cfg : Cfg129 G A c L b a K S) : resI L b ≤ K := cfg.hIK

end Basic

section Quot

variable {G : Type} [Group G] [Finite G] {A L K S : Subgroup G} {c b a : G}

@[expose] noncomputable def psiI (L K : Subgroup G) (b : G) (hIK : resI L b ≤ K) :
    ↥(resI L b) →* ↥K ⧸ aschbacherSolvableCore 3 ↥K :=
  (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K)).comp (Subgroup.inclusion hIK)

@[expose] noncomputable def Ibar (L K : Subgroup G) (b : G) (hIK : resI L b ≤ K) :
    Subgroup (↥K ⧸ aschbacherSolvableCore 3 ↥K) := (psiI L K b hIK).range

theorem psiI_apply (hIK : resI L b ≤ K) (x : ↥(resI L b)) :
    psiI L K b hIK x = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K) ⟨x, hIK x.2⟩ := rfl

theorem mk_mem_Ibar (hIK : resI L b ≤ K) {x : G} (hx : x ∈ resI L b) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K) (⟨x, hIK hx⟩ : ↥K) ∈ Ibar L K b hIK :=
  ⟨⟨x, hx⟩, rfl⟩

theorem isPerfect_Ibar (hIK : resI L b ≤ K) : Group.IsPerfect (Ibar L K b hIK) := by
  haveI := isPerfect_resI L b
  exact Group.IsPerfect.ofSurjective (f := (psiI L K b hIK).rangeRestrict)
    (psiI L K b hIK).rangeRestrict_surjective

theorem Ibar_le_centralizer (hIK : resI L b ≤ K) (hcK : c ∈ K)
    (hIc : resI L b ≤ Subgroup.centralizer ({c} : Set G)) :
    Ibar L K b hIK ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K) (⟨c, hcK⟩ : ↥K)} :
        Set (↥K ⧸ aschbacherSolvableCore 3 ↥K)) := by
  rintro _ ⟨x, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  change psiI L K b hIK x * _ = _ * psiI L K b hIK x
  rw [psiI_apply, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show (x : G) * c = c * x
  exact Subgroup.mem_centralizer_singleton_iff.mp (hIc x.2)

theorem Ibar_ne_top (hIK : resI L b ≤ K)
    (hlt : ¬ (resI L b ⊔ inSubgroup (aschbacherSolvableCore 3) K = K)) :
    Ibar L K b hIK ≠ ⊤ := by
  intro htop
  apply hlt
  refine le_antisymm (sup_le hIK (Subgroup.map_subtype_le _)) (fun k hk => ?_)
  have hmem : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K) (⟨k, hk⟩ : ↥K) ∈
      Ibar L K b hIK := htop ▸ Subgroup.mem_top _
  obtain ⟨i, hi⟩ := hmem
  have hθ : (Subgroup.inclusion hIK i)⁻¹ * (⟨k, hk⟩ : ↥K) ∈ aschbacherSolvableCore 3 ↥K :=
    QuotientGroup.eq.mp hi
  have hk' : k = (i : G) * (((Subgroup.inclusion hIK i)⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
  rw [hk']
  exact Subgroup.mul_mem_sup i.2 ⟨_, hθ, rfl⟩

@[expose] noncomputable def phiI (L : Subgroup G) (b : G) :
    ↥(resI L b) →* L ⧸ aschbacherSolvableCore 3 L :=
  (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion (resI_le_L L b))

theorem phiI_surjective (hX : L = resI L b ⊔ inSubgroup (aschbacherSolvableCore 3) L) :
    Function.Surjective (phiI L b) := by
  set θ₀ := aschbacherSolvableCore 3 ↥L with hθ₀
  have htop : (resI L b).subgroupOf L ⊔ θ₀ = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (resI_le_L L b),
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hX.symm
  have hmap : ((resI L b).subgroupOf L).map (QuotientGroup.mk' θ₀) = ⊤ := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' θ₀)) htop
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective θ₀),
      (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' θ₀).ge, sup_bot_eq] at h
    exact h
  intro q
  obtain ⟨t, ht, htq⟩ := (hmap ▸ Subgroup.mem_top q : q ∈ ((resI L b).subgroupOf L).map _)
  exact ⟨⟨(t : G), ht⟩, by rw [← htq]; rfl⟩

theorem ker_psiI_le_ker_phiI (hIK : resI L b ≤ K)
    (hLq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hφ : Function.Surjective (phiI L b)) :
    (psiI L K b hIK).ker ≤ (phiI L b).ker := by
  obtain ⟨hθs, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  set N₀ := (psiI L K b hIK).ker with hN₀
  let g : ↥N₀ →* ↥K := (Subgroup.inclusion hIK).comp N₀.subtype
  have hg : Function.Injective g :=
    (Subgroup.inclusion_injective hIK).comp N₀.subtype_injective
  have hgθ : ∀ x : ↥N₀, g x ∈ aschbacherSolvableCore 3 ↥K := fun x =>
    (QuotientGroup.eq_one_iff _).mp x.2
  let j : ↥N₀ →* ↥(aschbacherSolvableCore 3 ↥K) := g.codRestrict _ hgθ
  have hj : Function.Injective j := fun x y h => hg (congrArg Subtype.val h)
  haveI : Group.IsSolvable ↥(aschbacherSolvableCore 3 ↥K) := hθs
  haveI : Group.IsSolvable ↥N₀ := Group.isSolvable_of_isSolvable_injective hj
  have hN₀card : Nat.card N₀ ∣ Nat.card (aschbacherSolvableCore 3 ↥K) :=
    Subgroup.card_dvd_of_injective j hj
  set N₁ := N₀.map (phiI L b) with hN₁
  haveI : N₁.Normal := Subgroup.Normal.map inferInstance (phiI L b) hφ
  have hsurj : Function.Surjective ((phiI L b).subgroupMap N₀) :=
    (phiI L b).subgroupMap_surjective N₀
  haveI : Group.IsSolvable ↥N₁ := Group.isSolvable_of_surjective hsurj
  have hN₁c : N₁ ≤ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) :=
    Hering129HLift.solvable_normal_le_center hLq N₁ inferInstance
  have hcard1 : Nat.card N₁ ∣ Nat.card N₀ := Subgroup.card_dvd_of_surjective hsurj
  have hcard2 : Nat.card N₁ ∣ 3 := by
    have := Subgroup.card_dvd_of_le hN₁c
    rwa [hZ] at this
  have h13 : Nat.card N₁ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hcard2 with h | h
    · exact h
    · exfalso
      have h3 : 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥K) := by
        have := hcard1.trans hN₀card
        rwa [h] at this
      exact hθ3 h3
  have hbot : N₁ = ⊥ := Subgroup.card_eq_one.mp h13
  intro x hx
  have hx1 : phiI L b x ∈ N₁ := Subgroup.mem_map_of_mem _ hx
  rw [hbot, Subgroup.mem_bot] at hx1
  exact hx1

@[expose] noncomputable def fI (hIK : resI L b ≤ K) (hker : (psiI L K b hIK).ker ≤ (phiI L b).ker) :
    ↥(Ibar L K b hIK) →* L ⧸ aschbacherSolvableCore 3 L :=
  (psiI L K b hIK).rangeRestrict.liftOfSurjective (psiI L K b hIK).rangeRestrict_surjective
    ⟨phiI L b, by rwa [MonoidHom.ker_rangeRestrict]⟩

theorem fI_apply (hIK : resI L b ≤ K) (hker : (psiI L K b hIK).ker ≤ (phiI L b).ker)
    (x : ↥(resI L b)) :
    fI hIK hker ((psiI L K b hIK).rangeRestrict x) = phiI L b x := by
  unfold fI
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ (Function.rightInverse_surjInv _) _ x

end Quot

section Config

variable {G : Type} [Group G] [Finite G] {A L K S : Subgroup G} {c b a : G}

theorem isElemAbelian_A (cfg : Cfg129 G A c L b a K S) :
    CFSG.Assembly.IsElemAbelian 3 A := cfg.std.isE27.1

theorem comm_A (cfg : Cfg129 G A c L b a K S) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    x * y = y * x :=
  congrArg Subtype.val ((isElemAbelian_A cfg).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem c_mem_K (cfg : Cfg129 G A c L b a K S) : c ∈ K := (hIK_cfg cfg) (c_mem_resI cfg)

theorem a_mem_K (cfg : Cfg129 G A c L b a K S) : a ∈ K := (hIK_cfg cfg) (a_mem_resI cfg)

theorem K_le_centralizer_b (cfg : Cfg129 G A c L b a K S) :
    K ≤ Subgroup.centralizer ({b} : Set G) :=
  Sec6.le_centralizer_of_mem_thetaComponentsAt cfg.hK

theorem L_le_centralizer_c (cfg : Cfg129 G A c L b a K S) :
    L ≤ Subgroup.centralizer ({c} : Set G) :=
  Sec6.le_centralizer_of_mem_thetaComponentsAt cfg.std.mem_thetaComponentsAt

theorem resI_le_centralizer_c (cfg : Cfg129 G A c L b a K S) :
    resI L b ≤ Subgroup.centralizer ({c} : Set G) :=
  (resI_le_L L b).trans (L_le_centralizer_c cfg)

theorem c_pow (cfg : Cfg129 G A c L b a K S) : c ^ 3 = 1 :=
  (isElemAbelian_A cfg).2 c cfg.std.mem_A

theorem a_pow (cfg : Cfg129 G A c L b a K S) : a ^ 3 = 1 :=
  (isElemAbelian_A cfg).2 a cfg.ha.1

theorem b_pow (cfg : Cfg129 G A c L b a K S) : b ^ 3 = 1 :=
  (isElemAbelian_A cfg).2 b cfg.hb.1

theorem b_mem_A (cfg : Cfg129 G A c L b a K S) : b ∈ A := cfg.hb.1

theorem a_mem_A (cfg : Cfg129 G A c L b a K S) : a ∈ A := cfg.ha.1

theorem A_eq (cfg : Cfg129 G A c L b a K S) : A = Subgroup.zpowers b ⊔ (A ⊓ L) := by
  have hAe := (isElemAbelian_A cfg)
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, -⟩ := cfg.point_facts
  have hcA : c ∈ A := cfg.std.mem_A
  have hc1 : c ≠ 1 := cfg.std.ne_one
  have hcB : c ∈ A ⊓ Sec4.thetaQuotCentralizer L :=
    ⟨hcA, mem_thetaQuotCentralizer_of_central cfg.std.mem_L (L_le_centralizer_c cfg)⟩
  have hBeq : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers b ⊔ Subgroup.zpowers c :=
    (Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr cfg.hb) (Subgroup.zpowers_le.mpr hcB))
      (by rw [cfg.std.card_B, Proof128.card_zpowers_sup_eq_nine hAe hcA hbA hc1 hb1
        cfg.hb_not])).symm
  refine le_antisymm (fun y hy => ?_) (sup_le (Subgroup.zpowers_le.mpr hbA) inf_le_left)
  rw [← cfg.std.sup_eq, hBeq] at hy
  exact (sup_le (sup_le le_sup_left ((Subgroup.zpowers_le.mpr
    (⟨hcA, cfg.std.mem_L⟩ : c ∈ A ⊓ L)).trans le_sup_right)) le_sup_right) hy

theorem exists_decomp (cfg : Cfg129 G A c L b a K S) {d : G} (hd : d ∈ A) :
    ∃ j : ℤ, ∃ x ∈ A ⊓ L, d = b ^ j * x := by
  have hbc : ∀ f ∈ A ⊓ L, ∀ k : ℤ, (b ^ k) * f = f * b ^ k := fun f hf k =>
    ((Commute.zpow_left (show Commute b f from (comm_A cfg) (b_mem_A cfg) hf.1) k)).eq
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers b) (A ⊓ L) (fun u hu v hv => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact hbc v hv k)
  have hd' : d ∈ ((Subgroup.zpowers b ⊔ (A ⊓ L) : Subgroup G) : Set G) := (A_eq cfg) ▸ hd
  rw [hset] at hd'
  obtain ⟨u, hu, f, hf, rfl⟩ := hd'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  exact ⟨k, f, hf, rfl⟩

theorem AL_eq (cfg : Cfg129 G A c L b a K S) :
    A ⊓ L = Subgroup.zpowers a ⊔ Subgroup.zpowers c := by
  obtain ⟨hbA, haA, haL, hb1, ha1, -⟩ := cfg.point_facts
  have hcA : c ∈ A := cfg.std.mem_A
  symm
  refine Subgroup.eq_of_le_of_card_ge
    (sup_le (Subgroup.zpowers_le.mpr ⟨haA, haL⟩) (Subgroup.zpowers_le.mpr ⟨hcA, cfg.std.mem_L⟩)) ?_
  rw [card_inf_eq_nine_of_list cfg.std cfg.list, Proof128.card_zpowers_sup_eq_nine
    (isElemAbelian_A cfg) hcA haA cfg.std.ne_one ha1 cfg.ha_not]

end Config

section Elems

variable {G : Type} [Group G] [Finite G] {A L K S : Subgroup G} {c b a x y : G}

@[expose] noncomputable def barK (K : Subgroup G) (x : G) (hx : x ∈ K) :
    ↥K ⧸ aschbacherSolvableCore 3 ↥K :=
  QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K) ⟨x, hx⟩

theorem barK_zpow (hx : x ∈ K) (k : ℤ) :
    barK K (x ^ k) (K.zpow_mem hx k) = barK K x hx ^ k := by
  unfold barK
  rw [← map_zpow]
  rfl

theorem three_not_dvd_card_theta (K : Subgroup G) :
    ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥K) :=
  three_not_dvd_card_aschbacherSolvableCore

theorem orderOf_barK_eq_three (hx : x ∈ K) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    orderOf (barK K x hx) = 3 :=
  orderOf_mk_eq_three (aschbacherSolvableCore 3 ↥K) (three_not_dvd_card_theta K)
    (x := (⟨x, hx⟩ : ↥K)) (Subtype.ext (by simpa using hx3))
    (fun h => hx1 (congrArg Subtype.val h))

theorem barK_not_mem_zpowers (hx : x ∈ K) (hy : y ∈ K) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hnot : x ∉ Subgroup.zpowers y) :
    barK K x hx ∉ Subgroup.zpowers (barK K y hy) := by
  rintro ⟨k, hk⟩
  apply hnot
  set x' : ↥K := ⟨x, hx⟩
  set y' : ↥K := ⟨y, hy⟩
  have hx'3 : x' ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hy'3 : y' ^ 3 = 1 := Subtype.ext (by simpa using hy3)
  have hc : Commute x' y' := Subtype.ext hxy
  have hz : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K) (x'⁻¹ * y' ^ k) = 1 := by
    have : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K) (y' ^ k) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K) x' := by
      rw [map_zpow]
      exact hk
    rw [map_mul, map_inv, this, inv_mul_cancel]
  have hy3' : (x'⁻¹ * y' ^ k) ^ 3 = 1 := by
    rw [((hc.inv_left).zpow_right k).mul_pow, inv_pow, hx'3, inv_one, one_mul,
      ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy'3, one_zpow]
  have h1 := eq_one_of_mk_eq_one (aschbacherSolvableCore 3 ↥K) (three_not_dvd_card_theta K) hy3'
    hz
  have h2 : x' = y' ^ k := inv_mul_eq_one.mp h1
  have h3 : x = y ^ k := congrArg Subtype.val h2
  exact ⟨k, h3.symm⟩

end Elems

section Xbar

variable {G : Type} [Group G] [Finite G] {A L K S : Subgroup G} {c b a x y : G}

@[expose] noncomputable def Xbar (A K : Subgroup G) :
    Subgroup (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
  ((A ⊓ K).subgroupOf K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K))

theorem barK_mem_Xbar (hxA : x ∈ A) (hxK : x ∈ K) : barK K x hxK ∈ Xbar A K :=
  ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.mpr ⟨hxA, hxK⟩, rfl⟩

theorem le_Xbar (cfg : Cfg129 G A c L b a K S) :
    Subgroup.zpowers (barK K a (a_mem_K cfg)) ⊔ Subgroup.zpowers (barK K c (c_mem_K cfg)) ≤
      Xbar A K :=
  sup_le (Subgroup.zpowers_le.mpr (barK_mem_Xbar (a_mem_A cfg) (a_mem_K cfg)))
    (Subgroup.zpowers_le.mpr (barK_mem_Xbar cfg.std.mem_A (c_mem_K cfg)))

theorem Xbar_le_sup_center (cfg : Cfg129 G A c L b a K S) :
    Xbar A K ≤ (Subgroup.zpowers (barK K a (a_mem_K cfg)) ⊔
      Subgroup.zpowers (barK K c (c_mem_K cfg))) ⊔
        Subgroup.center (↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
  rintro _ ⟨w, hw, rfl⟩
  have hwA : (w : G) ∈ A := (Subgroup.mem_subgroupOf.mp hw).1
  obtain ⟨j, u, huAL, hwu⟩ := exists_decomp cfg hwA
  have huad : u ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c := (AL_eq cfg) ▸ huAL
  obtain ⟨i, k, hik⟩ := Sec4.exists_zpow_mul_of_mem_sup
    (comm_A cfg (a_mem_A cfg) cfg.std.mem_A) huad
  have haK := a_mem_K cfg
  have hcK := c_mem_K cfg
  have huK : u ∈ K := by
    rw [hik]
    exact K.mul_mem (K.zpow_mem haK i) (K.zpow_mem hcK k)
  have hbjK : b ^ j ∈ K := by
    have : b ^ j = (w : G) * u⁻¹ := by rw [hwu]; group
    rw [this]
    exact K.mul_mem w.2 (K.inv_mem huK)
  have hcentral : barK K (b ^ j) hbjK ∈ Subgroup.center (↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨q', rfl⟩ := QuotientGroup.mk_surjective q
    show QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K) q' *
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K) ⟨b ^ j, hbjK⟩ =
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K) ⟨b ^ j, hbjK⟩ *
          QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K) q'
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (q' : G) * b ^ j = b ^ j * q'
    have hq : (q' : G) ∈ Subgroup.centralizer ({b} : Set G) := K_le_centralizer_b cfg q'.2
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hq) j).eq
  have hu : barK K u huK ∈ Subgroup.zpowers (barK K a haK) ⊔ Subgroup.zpowers (barK K c hcK) := by
    have e : barK K u huK = barK K a haK ^ i * barK K c hcK ^ k := by
      have h1 := barK_zpow haK i
      have h2 := barK_zpow hcK k
      unfold barK at h1 h2 ⊢
      rw [← h1, ← h2, ← map_mul]
      congr 1
      exact Subtype.ext hik
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ _) (Subgroup.zpow_mem_zpowers _ _)
  have e : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K) w =
      barK K u huK * barK K (b ^ j) hbjK := by
    unfold barK
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    show (w : G) = u * b ^ j
    rw [hwu]
    exact ((Commute.zpow_left (show Commute b u from comm_A cfg (b_mem_A cfg) huAL.1) j).eq.symm
      ▸ rfl)
  rw [e]
  exact Subgroup.mul_mem_sup hu hcentral

end Xbar

section Beta

variable {G : Type} [Group G] [Finite G] {A L K S : Subgroup G} {c b a x y : G}

theorem maximal_A (cfg : Cfg129 G A c L b a K S) :
    ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A :=
  cfg.mem_S.1.2.1

theorem isPGroup_A (cfg : Cfg129 G A c L b a K S) : IsPGroup 3 A := fun d =>
  ⟨1, Subtype.ext (by simpa using (isElemAbelian_A cfg).2 d d.2)⟩

theorem beta_lift (cfg : Cfg129 G A c L b a K S)
    {t : ↥K ⧸ aschbacherSolvableCore 3 ↥K}
    (ht : t ∈ Subgroup.centralizer ((Subgroup.zpowers (barK K a (a_mem_K cfg)) ⊔
      Subgroup.zpowers (barK K c (c_mem_K cfg)) : Subgroup _) : Set _)) (ht3 : t ^ 3 = 1) :
    t ∈ Xbar A K := by
  have haK := a_mem_K cfg
  have hcK := c_mem_K cfg
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective t
  subst hy
  set θK := aschbacherSolvableCore 3 ↥K with hθK
  have hcomm : ∀ w ∈ Subgroup.zpowers (barK K a haK) ⊔ Subgroup.zpowers (barK K c hcK),
      w * (y : ↥K ⧸ θK) = (y : ↥K ⧸ θK) * w := fun w hw => Subgroup.mem_centralizer_iff.mp ht w hw
  set N : Subgroup G := inSubgroup (aschbacherSolvableCore 3) K with hN
  have hN3 : ¬ 3 ∣ Nat.card N := by
    rw [hN, inSubgroup, Subgroup.card_map_of_injective K.subtype_injective]
    exact three_not_dvd_card_theta K
  have hinv : ∀ d ∈ A, ∀ n ∈ N, ∃ n' ∈ N, d * ((y : G) * n) * d⁻¹ = (y : G) * n' := by
    intro d hd n hn
    obtain ⟨j, x, hxAL, rfl⟩ := exists_decomp cfg hd
    have hxK : x ∈ K := by
      have : x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c := (AL_eq cfg) ▸ hxAL
      obtain ⟨i, k, hik⟩ := Sec4.exists_zpow_mul_of_mem_sup
        (comm_A cfg (a_mem_A cfg) cfg.std.mem_A) this
      rw [hik]
      exact K.mul_mem (K.zpow_mem haK i) (K.zpow_mem hcK k)
    obtain ⟨ν, hν, rfl⟩ := hn
    set x' : ↥K := ⟨x, hxK⟩ with hx'
    have hxbar : barK K x hxK ∈ Subgroup.zpowers (barK K a haK) ⊔
        Subgroup.zpowers (barK K c hcK) := by
      have : x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c := (AL_eq cfg) ▸ hxAL
      obtain ⟨i, k, hik⟩ := Sec4.exists_zpow_mul_of_mem_sup
        (comm_A cfg (a_mem_A cfg) cfg.std.mem_A) this
      have e : barK K x hxK = barK K a haK ^ i * barK K c hcK ^ k := by
        have h1 := barK_zpow haK i
        have h2 := barK_zpow hcK k
        unfold barK at h1 h2 ⊢
        rw [← h1, ← h2, ← map_mul]
        congr 1
        exact Subtype.ext hik
      rw [e]
      exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ _) (Subgroup.zpow_mem_zpowers _ _)
    have h1 := hcomm _ hxbar
    have hm : y⁻¹ * (x' * y * x'⁻¹) ∈ θK := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change (y : ↥K ⧸ θK)⁻¹ * (barK K x hxK * (y : ↥K ⧸ θK) * (barK K x hxK)⁻¹) = 1
      rw [h1]
      group
    have hconj : x' * ν * x'⁻¹ ∈ θK := (inferInstance : θK.Normal).conj_mem ν hν x'
    refine ⟨((y⁻¹ * (x' * y * x'⁻¹)) * (x' * ν * x'⁻¹) : ↥K), ⟨_, θK.mul_mem hm hconj, rfl⟩, ?_⟩
    have hbx : ∀ w ∈ K, b ^ j * w * (b ^ j)⁻¹ = w := fun w hw => by
      have hc : Commute (b ^ j) w :=
        Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp
          (K_le_centralizer_b cfg hw)).symm j
      rw [hc.eq, mul_inv_cancel_right]
    have hkey : x * ((y : G) * ν) * x⁻¹ = ((y : G)) * (((y⁻¹ * (x' * y * x'⁻¹)) *
        (x' * ν * x'⁻¹) : ↥K) : G) := by
      have : x' * (y * ν) * x'⁻¹ = y * ((y⁻¹ * (x' * y * x'⁻¹)) * (x' * ν * x'⁻¹)) := by group
      exact congrArg Subtype.val this
    calc b ^ j * x * ((y : G) * ν) * (b ^ j * x)⁻¹
        = b ^ j * (x * ((y : G) * ν) * x⁻¹) * (b ^ j)⁻¹ := by group
      _ = x * ((y : G) * ν) * x⁻¹ :=
          hbx _ (K.mul_mem (K.mul_mem hxK (K.mul_mem y.2 ν.2)) (K.inv_mem hxK))
      _ = _ := hkey
  obtain ⟨n₀, hn₀N, hfix⟩ := exists_fixed_mem_coset (isPGroup_A cfg) hN3 (y : G) hinv
  obtain ⟨ν₀, hν₀, rfl⟩ := hn₀N
  set z : ↥K := y * ν₀ with hz
  have hν₀' : ν₀ ∈ θK := hν₀
  have hπz : QuotientGroup.mk' θK z = (y : ↥K ⧸ θK) := by
    change ((y * ν₀ : ↥K) : ↥K ⧸ θK) = (y : ↥K ⧸ θK)
    rw [QuotientGroup.eq]
    simpa [mul_inv_rev] using θK.inv_mem hν₀'
  have hzfix : ∀ d ∈ A, d * (z : G) = (z : G) * d := fun d hd => by
    have h := hfix d hd
    have h' : d * (z : G) * d⁻¹ = (z : G) := h
    calc d * (z : G) = d * (z : G) * d⁻¹ * d := by group
      _ = (z : G) * d := by rw [h']
  obtain ⟨s, hsz, ⟨r, hsr⟩, hsπ⟩ := exists_three_part_lift (QuotientGroup.mk' θK) (y := z)
    (by rw [hπz]; exact ht3)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hsz
  have hs3 : (z ^ k) ^ 3 = 1 := by
    have h1 : (z ^ k) ^ 3 ∈ θK := by
      rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' θK ((z ^ k) ^ 3) = 1
      rw [map_pow, hsπ, hπz, ht3]
    refine eq_one_of_pow_three_pow_of_mem (three_not_dvd_card_theta K) h1 (r := r) ?_
    rw [← pow_mul, mul_comm, pow_mul]
    exact (by rw [hsr, one_pow])
  have hscomm : ∀ d ∈ A, d * ((z ^ k : ↥K) : G) = ((z ^ k : ↥K) : G) * d := fun d hd => by
    have : Commute d (z : G) := hzfix d hd
    have h2 := (Commute.zpow_right this k)
    simpa using h2.eq
  have hs3' : ((z ^ k : ↥K) : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hs3
    simpa using this
  have hsA : ((z ^ k : ↥K) : G) ∈ A :=
    mem_of_maximal_elemAbelian (isElemAbelian_A cfg) (maximal_A cfg) hs3' hscomm
  refine ⟨z ^ k, Subgroup.mem_subgroupOf.mpr ⟨hsA, (z ^ k).2⟩, ?_⟩
  exact hsπ.trans hπz

end Beta

section Eps

variable {G : Type} [Group G] [Finite G] {A L K S : Subgroup G} {c b a x y : G}

theorem Ibar_eq_map (hIK : resI L b ≤ K) :
    Ibar L K b hIK =
      ((resI L b).subgroupOf K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K)) := by
  ext q
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨⟨i, hIK i.2⟩, Subgroup.mem_subgroupOf.mpr i.2, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, Subgroup.mem_subgroupOf.mp hw⟩, rfl⟩

theorem eps_lift (h125 : Item125BarC9) (cfg : Cfg129 G A c L b a K S)
    {Fb : Subgroup (↥K ⧸ aschbacherSolvableCore 3 ↥K)} (hFbI : Fb ≤ Ibar L K b (hIK_cfg cfg))
    (hFb : CFSG.Assembly.IsElemAbelian 3 Fb) (hFb9 : Nat.card Fb = 9)
    (hcFb : barK K c (c_mem_K cfg) ∈ Fb) :
    Subgroup.normalizer (Fb : Set (↥K ⧸ aschbacherSolvableCore 3 ↥K)) ≤
      Subgroup.normalizer (Subgroup.zpowers (barK K c (c_mem_K cfg)) :
        Set (↥K ⧸ aschbacherSolvableCore 3 ↥K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcK := c_mem_K cfg
  have hIK := (hIK_cfg cfg)
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, -⟩ := cfg.point_facts
  set θK := aschbacherSolvableCore 3 ↥K with hθK
  set π := QuotientGroup.mk' θK with hπ
  set c' : ↥K := ⟨c, hcK⟩ with hc'
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simpa using c_pow cfg)
  have hFbp : IsPGroup 3 Fb := fun x => ⟨1, Subtype.ext (by simpa using hFb.2 x x.2)⟩
  set M : Subgroup ↥K := (resI L b).subgroupOf K with hM
  have hBM : Fb ≤ M.map π := (Ibar_eq_map hIK) ▸ hFbI
  have hcM : c' ∈ M := Subgroup.mem_subgroupOf.mpr (c_mem_resI cfg)
  obtain ⟨S₀, hcS, hS₀M, hS₀3, hS₀F⟩ := Sec13.exists_isPGroup_le_map_eq (M := M) hFbp hBM
    (E := Subgroup.zpowers c') (isPGroup_zpowers_three hc'3) (Subgroup.zpowers_le.mpr hcM)
    (by rw [MonoidHom.map_zpowers]; exact Subgroup.zpowers_le.mpr hcFb)
  have hinj := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hS₀3
  have hS₀ab : CFSG.Assembly.IsElemAbelian 3 S₀ :=
    Sec13.isElemAbelian_of_injOn π hinj (hS₀F ▸ hFb)
  have hS₀9 : Nat.card S₀ = 9 := by
    rw [← Sec13.card_map_eq_of_injOn π hinj, hS₀F, hFb9]
  set Ft : Subgroup G := S₀.map K.subtype with hFt
  have hFtI : Ft ≤ resI L b := by
    rintro _ ⟨w, hw, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hS₀M hw)
  have hFtL : Ft ≤ L := hFtI.trans (resI_le_L L b)
  have hFtK : Ft ≤ K := Subgroup.map_subtype_le _
  have hFtab : CFSG.Assembly.IsElemAbelian 3 Ft := Sec13.isElemAbelian_map hS₀ab K.subtype
  have hFt9 : Nat.card Ft = 9 := by
    rw [hFt, Subgroup.card_map_of_injective K.subtype_injective, hS₀9]
  have hcFt : c ∈ Ft := ⟨c', hcS (Subgroup.mem_zpowers c'), rfl⟩
  have hbFt : b ∉ Ft := fun h => hbL (hFtL h)
  have hbcomm : ∀ y ∈ Ft, b * y = y * b := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (K_le_centralizer_b cfg (hFtK hy))).symm
  obtain ⟨hEab, hE27⟩ := Sec13.isElemAbelian_zpowers_sup_of_card_nine (b_pow cfg) (S := Ft)
    (Y := Ft) hbFt le_rfl hFt9 (fun s hs => hFtab.2 s hs) hbcomm
  set E : Subgroup G := Subgroup.zpowers b ⊔ Ft with hE
  have hcE : c ∈ E := Subgroup.mem_sup_right hcFt
  have hcA : c ∈ A := cfg.std.mem_A
  have hbcomm' : ∀ k : ℤ, b ^ k * c = c * b ^ k := fun k =>
    (Commute.zpow_left (show Commute b c from comm_A cfg (b_mem_A cfg) hcA) k).eq
  have hEL : E ≤ lcBar c L := by
    intro e he
    obtain ⟨k, f, hf, rfl⟩ := exists_zpow_mul_of_mem_sup_commute rfl hbcomm e he
    have hbk : b ^ k ∈ Sec4.thetaQuotCentralizer L :=
      (Sec4.thetaQuotCentralizer L).zpow_mem cfg.hb.2 k
    have hbkH : b ^ k ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
      mem_normalizer_zpowers_of_commute (hbcomm' k)
    have h1 := KS128NotHJTC.mul_mem_lcBar cfg.std.mem_thetaComponentsAt (hFtL hf) hbk hbkH
    have h2 : b ^ k * f = f * b ^ k := (Commute.zpow_left (hbcomm f hf) k).eq
    rw [h2]
    exact h1
  have hB9 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9 := by
    have hbc9 : Nat.card (Subgroup.zpowers b ⊔ Subgroup.zpowers c : Subgroup G) = 9 :=
      Proof128.card_zpowers_sup_eq_nine (isElemAbelian_A cfg) hcA (b_mem_A cfg) cfg.std.ne_one hb1
        cfg.hb_not
    have hcC : c ∈ Sec4.thetaQuotCentralizer L :=
      mem_thetaQuotCentralizer_of_central cfg.std.mem_L (L_le_centralizer_c cfg)
    have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers c ≤ E ⊓ Sec4.thetaQuotCentralizer L :=
      sup_le (Subgroup.zpowers_le.mpr ⟨Subgroup.mem_sup_left (Subgroup.mem_zpowers b), cfg.hb.2⟩)
        (Subgroup.zpowers_le.mpr ⟨hcE, hcC⟩)
    have hdvd : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE27]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hge : 9 ≤ Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := by
      rw [← hbc9]
      exact Subgroup.card_le_of_le hle
    have hne : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) ≠ 27 := by
      intro h27
      have hEC : E ⊓ Sec4.thetaQuotCentralizer L = E :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, hE27])
      have hEle : E ≤ Sec4.thetaQuotCentralizer L := hEC ▸ inf_le_right
      have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hEab.2 x x.2)⟩
      have h1 := card_inf_le_card_center_of_le_thetaQuotCentralizer hE3 hEle
      rw [card_center_eq_three_of_list cfg.list] at h1
      have h2 : Nat.card Ft ≤ Nat.card (E ⊓ L : Subgroup G) :=
        Subgroup.card_le_of_le (le_inf (le_sup_right : Ft ≤ E) hFtL)
      omega
    obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases j <;> simp_all <;> omega
  have hNE := h125 G A c L cfg.std cfg.list E ⟨hEab, hE27⟩ hEL hcE hB9
  have hN := Sec13.normalizer_map_mk_eq hS₀3
  rw [hS₀F] at hN
  intro nb hnb
  rw [hN] at hnb
  obtain ⟨n, hn, rfl⟩ := hnb
  have hnE : (n : G) ∈ Subgroup.normalizer (E : Set G) := by
    have hnF : (n : G) ∈ Subgroup.normalizer (Ft : Set G) := Sec13.mem_normalizer_map_subtype hn
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hnF ⊢
    rw [hE, Subgroup.map_sup, hnF, MonoidHom.map_zpowers]
    congr 2
    change (n : G) * b * (n : G)⁻¹ = b
    rw [Subgroup.mem_centralizer_singleton_iff.mp (K_le_centralizer_b cfg n.2),
      mul_inv_cancel_right]
  have hnc : (n : G) * c * (n : G)⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp (hNE hnE) c).mp (Subgroup.mem_zpowers c)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hnc
  have hmK : (n * c' * n⁻¹ : ↥K) = c' ^ m := Subtype.ext (by simpa using hm.symm)
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hconj : (n * c' ^ j * n⁻¹ : ↥K) = c' ^ (m * j) := by
    rw [← conj_zpow, hmK, ← zpow_mul]
  have hfin : π n * (π c') ^ j * (π n)⁻¹ = π c' ^ (m * j) := by
    rw [← map_zpow, ← map_inv, ← map_mul, ← map_mul, hconj, map_zpow]
  exact Subgroup.mem_zpowers_iff.mpr ⟨m * j, hfin.symm⟩

end Eps

section Subnormal

variable {G : Type} [Group G] [Finite G] {A L K S : Subgroup G} {c b a x y : G}

theorem resI_isSubnormal (cfg : Cfg129 G A c L b a K S) :
    ((resI L b).subgroupOf (K ⊓ Subgroup.centralizer ({c} : Set G))).IsSubnormal := by
  set Cc := Subgroup.centralizer ({c} : Set G) with hCc
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  set M : Subgroup G := Cc ⊓ Cb with hM
  obtain ⟨-, hL0⟩ := CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp
    cfg.std.mem_thetaComponentsAt
  have hLsub : (L.subgroupOf Cc).IsSubnormal := hL0.2.1
  have hLsubM : (L.subgroupOf M).IsSubnormal :=
    isSubnormal_subgroupOf_of_le (inf_le_left : M ≤ Cc) hLsub
  have hIL : resI L b ≤ L := resI_le_L L b
  have hle : (resI L b).subgroupOf M ≤ L.subgroupOf M := fun w hw =>
    Subgroup.mem_subgroupOf.mpr (hIL (Subgroup.mem_subgroupOf.mp hw))
  have hnorm : L.subgroupOf M ≤ Subgroup.normalizer (((resI L b).subgroupOf M : Subgroup M) :
      Set M) := by
    intro w hw
    have hwL : (w : G) ∈ L := Subgroup.mem_subgroupOf.mp hw
    have hwb : (w : G) ∈ Cb := w.2.2
    have hwN := le_normalizer_resI L b ⟨hwL, hwb⟩
    rw [Subgroup.mem_normalizer_iff] at hwN ⊢
    intro h
    exact hwN (h : G)
  have hIsub : ((resI L b).subgroupOf M).IsSubnormal :=
    Subgroup.IsSubnormal.step _ _ hle hLsubM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hnorm)
  have hKM : K ⊓ Cc ≤ M := fun x hx => ⟨hx.2, K_le_centralizer_b cfg hx.1⟩
  exact isSubnormal_subgroupOf_of_le hKM hIsub

theorem Ibar_isSubnormal (cfg : Cfg129 G A c L b a K S) :
    ((Ibar L K b (hIK_cfg cfg)).subgroupOf (Subgroup.centralizer
      ({barK K c (c_mem_K cfg)} : Set (↥K ⧸ aschbacherSolvableCore 3 ↥K)))).IsSubnormal := by
  have hcK := c_mem_K cfg
  set Cc := Subgroup.centralizer ({c} : Set G) with hCc
  set θK := aschbacherSolvableCore 3 ↥K with hθK
  set π := QuotientGroup.mk' θK with hπ
  set c' : ↥K := ⟨c, hcK⟩ with hc'
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simpa using c_pow cfg)
  have h1 := resI_isSubnormal cfg
  have h2 := isSubnormal_subgroupOf_subgroupOf (H := resI L b) (N := K ⊓ Cc) (K := K)
    inf_le_left h1
  have hSV : (resI L b).subgroupOf K ≤ (K ⊓ Cc).subgroupOf K := fun w hw =>
    Subgroup.mem_subgroupOf.mpr ⟨w.2, resI_le_centralizer_c cfg (Subgroup.mem_subgroupOf.mp hw)⟩
  have h3 := isSubnormal_map_subgroupOf π hSV h2
  have hV : (K ⊓ Cc).subgroupOf K = Subgroup.centralizer ({c'} : Set ↥K) := by
    ext w
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨w.2, congrArg Subtype.val h⟩
  rw [hV, Hering129HLift.map_centralizer_eq θK (three_not_dvd_card_theta K) hc'3,
    ← Ibar_eq_map (hIK_cfg cfg)] at h3
  exact h3

end Subnormal

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
