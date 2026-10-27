module

import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec13.Item131bProofE

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem exists_subgroup_comm_zpowers {G : Type} [Group G] {E Z : Subgroup G}
    (hZE : ∀ z ∈ Z, ∀ e ∈ E, e * z = z * e) :
    ∃ K : Subgroup G, ∀ f, f ∈ K ↔
      (f ∈ Subgroup.centralizer (Z : Set G) ∧ ∀ e ∈ E, f * e * f⁻¹ * e⁻¹ ∈ Z) := by
  obtain ⟨S, hS⟩ : ∃ S : Set G, S = {f | f ∈ Subgroup.centralizer (Z : Set G) ∧
      ∀ e ∈ E, f * e * f⁻¹ * e⁻¹ ∈ Z} := ⟨_, rfl⟩
  have hmem : ∀ f, f ∈ S ↔
      (f ∈ Subgroup.centralizer (Z : Set G) ∧ ∀ e ∈ E, f * e * f⁻¹ * e⁻¹ ∈ Z) := by
    intro f
    rw [hS]
    rfl
  have hmul : ∀ f1 f2, f1 ∈ S → f2 ∈ S → f1 * f2 ∈ S := by
    intro f1 f2 h1 h2
    obtain ⟨hf1, hf1e⟩ := (hmem f1).mp h1
    obtain ⟨hf2, hf2e⟩ := (hmem f2).mp h2
    refine (hmem (f1 * f2)).mpr ⟨Subgroup.mul_mem _ hf1 hf2, fun e he => ?_⟩
    have h1' := hf1e e he
    have h2' := hf2e e he
    have hc : f1 * (f2 * e * f2⁻¹ * e⁻¹) * f1⁻¹ = f2 * e * f2⁻¹ * e⁻¹ := by
      have hcom := (Subgroup.mem_centralizer_iff.mp hf1) (f2 * e * f2⁻¹ * e⁻¹) h2'
      rw [← hcom]
      group
    have hid : f1 * f2 * e * (f1 * f2)⁻¹ * e⁻¹ =
        (f1 * (f2 * e * f2⁻¹ * e⁻¹) * f1⁻¹) * (f1 * e * f1⁻¹ * e⁻¹) := by
      group
    show f1 * f2 * e * (f1 * f2)⁻¹ * e⁻¹ ∈ Z
    rw [hid, hc]
    exact Subgroup.mul_mem _ h2' h1'
  have hone : (1 : G) ∈ S := by
    refine (hmem 1).mpr ⟨Subgroup.one_mem _, fun e _ => ?_⟩
    have h1 : (1 : G) * e * (1 : G)⁻¹ * e⁻¹ = 1 := by group
    show (1 : G) * e * (1 : G)⁻¹ * e⁻¹ ∈ Z
    rw [h1]
    exact Subgroup.one_mem _
  have hinv : ∀ f, f ∈ S → f⁻¹ ∈ S := by
    intro f h
    obtain ⟨hf, hfe⟩ := (hmem f).mp h
    refine (hmem f⁻¹).mpr ⟨Subgroup.inv_mem _ hf, fun e he => ?_⟩
    have hw : f * e⁻¹ * f⁻¹ * e ∈ Z := by
      have h' := hfe e⁻¹ (Subgroup.inv_mem _ he)
      rwa [inv_inv] at h'
    have hwe : e * (f * e⁻¹ * f⁻¹ * e) = (f * e⁻¹ * f⁻¹ * e) * e := hZE _ hw e he
    have hwf : (f * e⁻¹ * f⁻¹ * e) * f = f * (f * e⁻¹ * f⁻¹ * e) :=
      (Subgroup.mem_centralizer_iff.mp hf) (f * e⁻¹ * f⁻¹ * e) hw
    have hef : e * f * e⁻¹ * f⁻¹ = f * e⁻¹ * f⁻¹ * e := by
      calc e * f * e⁻¹ * f⁻¹ = e * (f * e⁻¹ * f⁻¹ * e) * e⁻¹ := by group
        _ = f * e⁻¹ * f⁻¹ * e := by rw [hwe]; group
    have hgoal : f⁻¹ * e * (f⁻¹)⁻¹ * e⁻¹ = f⁻¹ * (e * f * e⁻¹ * f⁻¹) * f := by
      group
    have hfin : f⁻¹ * (f * e⁻¹ * f⁻¹ * e) * f = f * e⁻¹ * f⁻¹ * e := by
      calc f⁻¹ * (f * e⁻¹ * f⁻¹ * e) * f = f⁻¹ * ((f * e⁻¹ * f⁻¹ * e) * f) := by group
        _ = f⁻¹ * (f * (f * e⁻¹ * f⁻¹ * e)) := by rw [hwf]
        _ = f * e⁻¹ * f⁻¹ * e := by group
    show f⁻¹ * e * (f⁻¹)⁻¹ * e⁻¹ ∈ Z
    rw [hgoal, hef, hfin]
    exact hw
  have hmul' : ∀ {f1 f2 : G}, f1 ∈ S → f2 ∈ S → f1 * f2 ∈ S :=
    fun h1 h2 => hmul _ _ h1 h2
  have hinv' : ∀ {f : G}, f ∈ S → f⁻¹ ∈ S := fun h => hinv _ h
  exact ⟨{ carrier := S,
           mul_mem' := hmul',
           one_mem' := hone,
           inv_mem' := hinv' }, fun f => hmem f⟩

theorem exists_F {G : Type} [Group G] [Finite G] (hFE : partTwoF G = partTwoE G)
    {E : Subgroup G} {a c : G} (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hE : E ∉ partTwoE G) (hcE : c ∈ E) (haE : a ∉ E) (ha3 : a ^ 3 = 1)
    (hcomm : ∀ e ∈ E, a * e * a⁻¹ * e⁻¹ ∈ Subgroup.zpowers c) (hac : a * c = c * a)
    (hev : 2 ∣ Nat.card
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)))) :
    ∃ F : Subgroup G, CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 27 ∧ a ∈ F ∧ c ∈ F ∧
      F ≤ Subgroup.centralizer ({a} : Set G) ∧ F ∈ partTwoF G ∧ F ∉ partTwoT G ∧
      E ≤ Subgroup.normalizer (F : Set G) ∧ F ≤ Subgroup.normalizer (E : Set G) ∧
      (∀ f ∈ F, ∀ e ∈ E, f * e * f⁻¹ * e⁻¹ ∈ Subgroup.zpowers c) ∧
      Nat.card (E ⊓ F : Subgroup G) = 9 ∧ F = Subgroup.zpowers a ⊔ (E ⊓ F) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := hEe.2
  have hc3 : c ^ 3 = 1 := hE3 c hcE
  have hZE : ∀ z ∈ Subgroup.zpowers c, ∀ e ∈ E, e * z = z * e := by
    intro z hz e he
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((show Commute e c from hEcomm e he c hcE).zpow_right j).eq
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup G, C = E ⊓ Subgroup.centralizer ({a} : Set G) :=
    ⟨_, rfl⟩
  have hCE : C ≤ E := by rw [hCdef]; exact inf_le_left
  have hCcent : C ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [hCdef]; exact inf_le_right
  have hCmem : ∀ x ∈ C, x ∈ E ∧ x * a = a * x := fun x hx =>
    ⟨hCE hx, Subgroup.mem_centralizer_singleton_iff.mp (hCcent hx)⟩
  have hcC : c ∈ C := by
    rw [hCdef]
    exact Subgroup.mem_inf.mpr ⟨hcE, Subgroup.mem_centralizer_singleton_iff.mpr hac.symm⟩
  have hkmem : ∀ x : E, a * (x : G) * a⁻¹ * (x : G)⁻¹ ∈ Subgroup.zpowers c :=
    fun x => hcomm x x.2
  let k : E →* G :=
    { toFun := fun x => a * (x : G) * a⁻¹ * (x : G)⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        have hw : (x : G) * (a * (y : G) * a⁻¹ * (y : G)⁻¹) =
            (a * (y : G) * a⁻¹ * (y : G)⁻¹) * (x : G) :=
          hZE _ (hkmem y) (x : G) x.2
        have hxw : (x : G) * (a * (y : G) * a⁻¹ * (y : G)⁻¹) * (x : G)⁻¹ =
            a * (y : G) * a⁻¹ * (y : G)⁻¹ := by
          rw [hw, mul_inv_cancel_right]
        show a * ((x : G) * (y : G)) * a⁻¹ * ((x : G) * (y : G))⁻¹ =
          (a * (x : G) * a⁻¹ * (x : G)⁻¹) * (a * (y : G) * a⁻¹ * (y : G)⁻¹)
        calc a * ((x : G) * (y : G)) * a⁻¹ * ((x : G) * (y : G))⁻¹
            = (a * (x : G) * a⁻¹ * (x : G)⁻¹) *
                ((x : G) * (a * (y : G) * a⁻¹ * (y : G)⁻¹) * (x : G)⁻¹) := by group
          _ = (a * (x : G) * a⁻¹ * (x : G)⁻¹) * (a * (y : G) * a⁻¹ * (y : G)⁻¹) := by
            rw [hxw] }
  have hkrange : k.range ≤ Subgroup.zpowers c := by
    intro g hg
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg
    exact hkmem x
  have hdvd3 : Nat.card k.range ∣ 3 := by
    have h1 := Subgroup.card_dvd_of_le hkrange
    rw [Nat.card_zpowers] at h1
    exact h1.trans (orderOf_dvd_of_pow_eq_one hc3)
  have hquot : Nat.card (↥E ⧸ k.ker) = Nat.card k.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange k).toEquiv
  have hkerC : (k.ker.map E.subtype : Subgroup G) = C := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx1 : a * (x : G) * a⁻¹ * (x : G)⁻¹ = 1 := MonoidHom.mem_ker.mp hx
      have hxa : a * (x : G) = (x : G) * a := by
        calc a * (x : G) = (a * (x : G) * a⁻¹ * (x : G)⁻¹) * (x : G) * a := by group
          _ = (x : G) * a := by rw [hx1, one_mul]
      rw [hCdef, Subgroup.mem_inf]
      exact ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr hxa.symm⟩
    · intro hg
      obtain ⟨hgE, hga⟩ := hCmem g hg
      refine ⟨⟨g, hgE⟩, ?_, rfl⟩
      refine MonoidHom.mem_ker.mpr ?_
      show a * g * a⁻¹ * g⁻¹ = 1
      rw [← hga]
      group
  have hcardker : Nat.card k.ker = Nat.card C := by
    rw [← hkerC]
    exact (Subgroup.card_map_of_injective E.subtype_injective).symm
  have hm : Nat.card (↥E ⧸ k.ker) ∣ 3 := by
    rw [hquot]; exact hdvd3
  have hC_card : 27 = Nat.card (↥E ⧸ k.ker) * Nat.card C := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup k.ker
    rw [hE27, hcardker] at h
    exact h
  have hC9 : Nat.card C = 9 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hm with h1 | h1
    · exfalso
      rw [h1, one_mul] at hC_card
      have hCE' : C = E := Subgroup.eq_of_le_of_card_ge hCE (by omega)
      have hEcent : E ≤ Subgroup.centralizer ({a} : Set G) := by
        rw [← hCE']; exact hCcent
      exact hE (CFSG.RankThree.PartTwo.Sec13.Item131bProof.mem_partTwoE_of_le_centralizer
        hEe hE27 hEcent hev)
    · rw [h1] at hC_card
      omega
  have hCe : CFSG.Assembly.IsElemAbelian 3 C := by
    refine ⟨?_, fun x hx => hE3 x (hCE hx)⟩
    rw [← Subgroup.le_centralizer_iff_isMulCommutative]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hEcomm y (hCE hy) x (hCE hx)
  have haC : a ∉ C := fun h => haE (hCE h)
  obtain ⟨F, hFdef⟩ : ∃ F : Subgroup G, F = C ⊔ Subgroup.zpowers a := ⟨_, rfl⟩
  have hsup := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hCe haC ha3
    (fun x hx => (hCmem x hx).2)
  have hFab : CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 27 := by
    rw [hFdef]
    exact ⟨hsup.1, by rw [hsup.2]; omega⟩
  have haF : a ∈ F := by
    rw [hFdef]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hcF : c ∈ F := by
    rw [hFdef]; exact Subgroup.mem_sup_left hcC
  have hFcent : F ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [hFdef]
    exact sup_le hCcent (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  have hFpE : F ∈ partTwoE G :=
    CFSG.RankThree.PartTwo.Sec13.Item131bProof.mem_partTwoE_of_le_centralizer hFab.1 hFab.2
      hFcent hev
  have hFF : F ∈ partTwoF G := by
    rw [hFE]; exact hFpE
  have hEF_ne : E ⊓ F ≠ E := by
    intro h
    have hEF' : E ≤ F := inf_eq_left.mp h
    exact hE (CFSG.RankThree.PartTwo.Sec13.Item131bProof.mem_partTwoE_of_le_centralizer hEe hE27
      (hEF'.trans hFcent) hev)
  have hC_le_EF : C ≤ E ⊓ F := le_inf hCE (by rw [hFdef]; exact le_sup_left)
  have hEF9 : Nat.card (E ⊓ F : Subgroup G) = 9 := by
    have hdvd : Nat.card (E ⊓ F : Subgroup G) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE27]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h9 : 9 ∣ Nat.card (E ⊓ F : Subgroup G) := by
      have h := Subgroup.card_dvd_of_le hC_le_EF
      rwa [hC9] at h
    obtain ⟨i, hi, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases i
    · rw [hn] at h9; norm_num at h9
    · rw [hn] at h9; norm_num at h9
    · rw [hn]; norm_num
    · exfalso
      exact hEF_ne (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hE27, hn]; norm_num))
  have hEF : E ⊓ F = C := (Subgroup.eq_of_le_of_card_ge hC_le_EF (by omega)).symm
  have hFgen : F = Subgroup.zpowers a ⊔ (E ⊓ F) := by
    rw [hEF, hFdef, sup_comm]
  have hu : ∀ e ∈ E, a * e⁻¹ * a⁻¹ * e ∈ Subgroup.zpowers c := by
    intro e he
    have h := hcomm e⁻¹ (Subgroup.inv_mem _ he)
    rwa [inv_inv] at h
  have hkey : ∀ e ∈ E, e * a * e⁻¹ = (a * e⁻¹ * a⁻¹ * e) * a := by
    intro e he
    have hcu : e * (a * e⁻¹ * a⁻¹ * e) = (a * e⁻¹ * a⁻¹ * e) * e := hZE _ (hu e he) e he
    calc e * a * e⁻¹ = (e * (a * e⁻¹ * a⁻¹ * e) * e⁻¹) * a := by group
      _ = (a * e⁻¹ * a⁻¹ * e) * a := by rw [hcu]; group
  have hstab : ∀ e ∈ E, ∀ f ∈ F, e * f * e⁻¹ ∈ F := by
    intro e he f hf
    rw [hFdef] at hf ⊢
    have hle : C ⊔ Subgroup.zpowers a ≤
        (C ⊔ Subgroup.zpowers a).comap (MulAut.conj e).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro x hx
        show e * x * e⁻¹ ∈ C ⊔ Subgroup.zpowers a
        have hxe : e * x * e⁻¹ = x := by
          rw [hEcomm e he x (hCE hx), mul_inv_cancel_right]
        rw [hxe]
        exact Subgroup.mem_sup_left hx
      · rw [Subgroup.zpowers_le]
        show e * a * e⁻¹ ∈ C ⊔ Subgroup.zpowers a
        rw [hkey e he]
        exact Subgroup.mul_mem _
          (Subgroup.mem_sup_left (Subgroup.zpowers_le.mpr hcC (hu e he)))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
    exact hle hf
  have hEnorm : E ≤ Subgroup.normalizer (F : Set G) := fun e he =>
    Subgroup.mem_normalizer_fintype fun n hn => hstab e he n hn
  have ha_norm : a ∈ Subgroup.normalizer (E : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hzE : a * n * a⁻¹ * n⁻¹ ∈ E := Subgroup.zpowers_le.mpr hcE (hcomm n hn)
    have hid : a * n * a⁻¹ = (a * n * a⁻¹ * n⁻¹) * n := by group
    rw [hid]
    exact E.mul_mem hzE hn
  have hFnorm : F ≤ Subgroup.normalizer (E : Set G) := by
    rw [hFdef]
    exact sup_le (hCE.trans Subgroup.le_normalizer) (Subgroup.zpowers_le.mpr ha_norm)
  have hZcent : ∀ g : G, c * g = g * c → ∀ z ∈ Subgroup.zpowers c, z * g = g * z := by
    intro g hg z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((show Commute c g from hg).zpow_left j).eq
  obtain ⟨K, hK⟩ := exists_subgroup_comm_zpowers (E := E) (Z := Subgroup.zpowers c) hZE
  have hCK : C ≤ K := by
    intro x hx
    rw [hK]
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun z hz => (hZE z hz x (hCE hx)).symm,
      fun e he => ?_⟩
    have hxe : x * e * x⁻¹ * e⁻¹ = 1 := by
      rw [hEcomm x (hCE hx) e he]
      group
    rw [hxe]
    exact Subgroup.one_mem _
  have haK : a ∈ K := by
    rw [hK]
    exact ⟨Subgroup.mem_centralizer_iff.mpr fun z hz => hZcent a hac.symm z hz, hcomm⟩
  have hFK : F ≤ K := by
    rw [hFdef]
    exact sup_le hCK (Subgroup.zpowers_le.mpr haK)
  have hFcomm : ∀ f ∈ F, ∀ e ∈ E, f * e * f⁻¹ * e⁻¹ ∈ Subgroup.zpowers c :=
    fun f hf => ((hK f).mp (hFK hf)).2
  have hFT : F ∉ partTwoT G := by
    rintro ⟨-, H, hH, hHle⟩
    obtain ⟨P, hP1, hP2, rfl⟩ := hH
    exact hE ⟨hEe, hE27, P, hP1, hP2,
      hEnorm.trans ((CFSG.RankThree.PartTwo.Sec13.Item131bProof.normalizer_le_aschCore_self
        hFab.1 hFab.2).trans hHle)⟩
  exact ⟨F, hFab.1, hFab.2, haF, hcF, hFcent, hFF, hFT, hEnorm, hFnorm, hFcomm, hEF9, hFgen⟩

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
