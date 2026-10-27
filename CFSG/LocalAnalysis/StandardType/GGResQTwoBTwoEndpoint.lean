module

public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineTransfer
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineAux
public import CFSG.LocalAnalysis.StandardType.GGPZTrivJ
public import CFSG.LocalAnalysis.StandardType.GGPZVertHolds
public import CFSG.LocalAnalysis.StandardType.GGPumpupBalance
public import CFSG.LocalAnalysis.StandardType.GGR4Forced
public import CFSG.LocalAnalysis.StandardType.GGR4PComp
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGen
public import CFSG.LocalAnalysis.StandardType.GGResIFixJ
public import CFSG.LocalAnalysis.StandardType.GGPZReflNormal
public import CFSG.LocalAnalysis.StandardType.GGResQTwoBTwoForced
public import CFSG.LocalAnalysis.StandardType.GGResQTwoTransport
public import CFSG.LocalAnalysis.StandardType.GGTbKlJ
public import CFSG.LocalAnalysis.StandardType.GGAm2Final
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.CGT.PushingUpLit.CGT6.SixFourA8
public import CFSG.GH74.GLS.Stage4.Q9.Rigidity
public import CFSG.Quasithin.Vol2.Ch10SecB3CHall
public import CFSG.Quasithin.Vol2.Ch10SecB3GL4
public import CFSG.Quasithin.Vol2.Ch10SecB3SixZ
public import CFSG.Quasithin.Vol2.Ch10SecE22OneB
public import CFSG.Quasithin.Vol2.Ch10SecEBlockA5
public import CFSG.Quasithin.Vol2.Ch10SecEOver
public import CFSG.Quasithin.Vol2.Ch10SecQ4FS2
public import CFSG.Quasithin.Vol2.Ch10SecQ4FS3
public import CFSG.Quasithin.Vol2.Ch10SecQ4FS9
public import CFSG.Quasithin.Vol2.Ch10SecQ4H4
public import CFSG.Quasithin.Vol2.Ch11SecBBasic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggBTwoCard_le_of_lineDatum {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    (hBsJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hJT : GGResLineJDatum 3 Bs J .B2) :
    9 ≤ Nat.card (Bs ⊓ J : Subgroup G) := by
  obtain ⟨V, instV, instM, ι, r, hv, hα, hvec, hrefl, hcart, hind, hgen⟩ := hJT
  have hdiag : ∀ j : Fin 2, hα j (hv j) = (2 : ZMod 3) := by
    intro j
    rw [hcart j j]
    fin_cases j <;> norm_num [GGResLineJType.cartan, CartanMatrix.B]
  have hmem : ∀ j : Fin 2, ((Additive.toMul (ι.symm (hv j)) : ↥Bs) : G) ∈ J := by
    intro j
    have hφJ : r j ∈ ggAutomizer J Bs := by
      rw [hgen]
      exact Subgroup.subset_closure ⟨j, rfl⟩
    exact ggCoroot_mem (p := 3) (by norm_num) hBsJ ι (hvec j) (hdiag j) hφJ
  have h := ggCoroots_card_le (p := 3) (Bs := Bs) (X := J) ι (hv := hv) hind hmem
  norm_num at h
  exact h

theorem ggBTwoPumpEndpoint_order_bound
    {G : Type} [Group G] [Finite G]
    (hLB : GGLBalanceInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hPL : ∀ (z : G) (X : Subgroup G), GGNbr 3 B x D J z X → J ≤ X →
      ¬ 9 ∣ Nat.card (ggAutomizer X Bs))
    (hH : GGResHyp 3 B Bs x L D J y K)
    (_hLD : GGResLeviDatum 3 Bs L J K ggSelI (ggTypRankLt 8))
    (hJT : GGResLineJDatum 3 Bs J .B2)
    (hcardBs : Nat.card Bs = 81)
    (hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥J))
    {z : G} (hzD : z ∈ D) (hzx : z ∉ Subgroup.zpowers x) :
    let X := ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J
    LargeEvenPComponent 3 (Subgroup.centralizer ({z} : Set G)) X ∧
      J ≤ X ∧ Bs ≤ Subgroup.normalizer (X : Set G) ∧
      ¬ 9 ∣ Nat.card (ggAutomizer X Bs) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hCfg, -, hIDAll, -, -, -, -⟩ := hH
  have hBstar : GGBstar 3 B Bs := hCfg.2.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hCfg.2.2
  have hI : GGThmIHyp 3 B x L := hCfg.1
  have hS : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hInn : GGInnerDiagOn Bs L := hIDAll.1
  have hBeq : B = Bs := by
    obtain ⟨⟨-, -, -, -, -, hβ, hSstar, -⟩, hBs, -⟩ := hCfg
    have hBcard : Nat.card B = 3 ^ CFSG.Open.twoLocalPrimeRank 3 G := hSstar.1.2.1
    have h4 : 4 ≤ CFSG.Open.twoLocalPrimeRank 3 G := hβ.2.2.2
    apply Subgroup.eq_of_le_of_card_ge hBs.1
    rw [hcardBs, hBcard, show (81 : ℕ) = 3 ^ 4 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) h4
  have hD : Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
    obtain ⟨-, -, -, -, -, -, hDlast⟩ := hDJ.1
    rw [← hBeq, ← hDlast]
  have hDBs : D ≤ Bs := hDJ.1.1.trans hBstar.1
  have hDcent : D ≤ Subgroup.centralizer (J : Set G) := by
    rw [← hD]
    exact inf_le_right
  have hDcard : Nat.card D = 9 := by
    have h := hDJ.1.2.2.1
    rw [h]
    norm_num
  have hint : (Bs ⊓ J) ⊓ D = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun d hd => ?_
    by_contra hd1
    have hdJ : d ∈ J := hd.1.2
    have hdp : d ^ 3 = 1 := hDJ.1.2.1.2 d hd.2
    have hdc : (⟨d, hdJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (by simpa using (Subgroup.mem_centralizer_iff.mp (hDcent hd.2) g g.2))
    have hord : orderOf d = 3 := orderOf_eq_prime hdp hd1
    have hdvd : orderOf (⟨⟨d, hdJ⟩, hdc⟩ : ↥(Subgroup.center ↥J)) ∣
        Nat.card ↥(Subgroup.center ↥J) :=
      orderOf_dvd_natCard _
    have hordc : orderOf (⟨⟨d, hdJ⟩, hdc⟩ : ↥(Subgroup.center ↥J)) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hord]
    exact hZ (hordc ▸ hdvd)
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) := ggR4_normalizes_J hCfg hInn
  have hge9 : 9 ≤ Nat.card (Bs ⊓ J : Subgroup G) :=
    ggBTwoCard_le_of_lineDatum hBsJ hJT
  let F : ↥(Bs ⊓ J) × ↥D → ↥Bs := fun ad =>
    ⟨(ad.1 : G) * (ad.2 : G), Bs.mul_mem ad.1.2.1 (hDBs ad.2.2)⟩
  have hFinj : Function.Injective F := by
    rintro ⟨a, d⟩ ⟨a', d'⟩ hF
    have h1 : (a : G) * d = a' * d' := congrArg Subtype.val hF
    have h2 : (a' : G)⁻¹ * a = d' * (d : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * d) * (d : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * d') * (d : G)⁻¹ := by rw [h1]
        _ = d' * (d : G)⁻¹ := by group
    have h3 : (a' : G)⁻¹ * a ∈ (Bs ⊓ J) ⊓ D :=
      ⟨(Bs ⊓ J).mul_mem ((Bs ⊓ J).inv_mem a'.2) a.2, h2 ▸ D.mul_mem d'.2 (D.inv_mem d.2)⟩
    rw [hint, Subgroup.mem_bot] at h3
    have h4 : (a : G) = a' := (inv_mul_eq_one.mp h3).symm
    have h5 : (d : G) = d' := by
      rw [h3] at h2
      have h6 : (d' : G) * (d : G)⁻¹ = 1 := h2.symm
      exact (mul_inv_eq_one.mp h6).symm
    exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)
  have hAle : Nat.card ↥(Bs ⊓ J) ≤ 9 := by
    have hle := Nat.card_le_card_of_injective F hFinj
    rw [Nat.card_prod, hDcard, hcardBs] at hle
    omega
  have hcardEJ : Nat.card ↥(Bs ⊓ J) = 9 := le_antisymm hAle (by simpa using hge9)
  have hsurj : Function.Surjective F :=
    (hFinj.bijective_of_nat_card_le (by
      rw [Nat.card_prod, hcardEJ, hDcard, hcardBs])).2
  have hprod : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ J, ∃ d ∈ D, b = a * d := by
    intro b hb
    obtain ⟨⟨a, d⟩, hF⟩ := hsurj ⟨b, hb⟩
    exact ⟨a, a.2, d, d.2, (congrArg Subtype.val hF).symm⟩
  have hED : Bs = (Bs ⊓ J) ⊔ D := by
    refine le_antisymm (fun b hb => ?_) (sup_le inf_le_left hDBs)
    obtain ⟨a, ha, d, hd, rfl⟩ := hprod b hb
    exact Subgroup.mul_mem_sup ha hd
  have hpJ : 3 ∣ Nat.card ↥J := by
    have h9 : 9 ∣ Nat.card ↥J :=
      hcardEJ ▸ Subgroup.card_dvd_of_le (inf_le_right : Bs ⊓ J ≤ J)
    exact (by norm_num : 3 ∣ 9).trans h9
  have hDcz : D = Subgroup.closure {x, z} := eq_closure_pair_of_mem hI hDJ hzD hzx
  obtain ⟨hXp, hJX, hxN, hbranch⟩ :=
    pumpup_of_stdSub (ggPumpupInput_of_lBalance hLB) hI hDJ hpJ hDcz
  have hzBs : z ∈ Bs := hDBs hzD
  have hBsC : Bs ≤ Subgroup.centralizer ({z} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hBstar.2.1.1.is_comm.comm ⟨b, hb⟩ ⟨z, hzBs⟩))
  have hBsNX : Bs ≤ Subgroup.normalizer
      (ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J : Set G) :=
    ggLayerClosure_normalized hBsC hBsJ
  refine ⟨hXp, hJX, hBsNX, ?_⟩
  rcases hbranch with hNb | hcomm
  ·
    have h := hPL z
      (ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J) hNb hJX
    simpa [GGResLineJType.bad] using h
  ·
    have hJcomp : IsComponentOf J (Subgroup.centralizer ({z} : Set G) ⊓
        Subgroup.centralizer ({x} : Set G)) :=
      isComponentOf_inf_centralizer_of_stdSub hS hDJ.1 hDcz
    have hJq : CFSG.IsQuasisimple ↥J :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).1
        hJcomp.2.2
    have hJP : LargeEvenPComponent 3
        (ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J ⊓
          Subgroup.centralizer ({x} : Set G)) J :=
      ggJ_pComponent_centralizer hI hDJ hpJ hDcz hXp hJX
    have hxp : x ^ 3 = 1 := hS.1.1.2 x hS.2.1
    have hx1 : x ≠ 1 := hS.2.2.1
    have hYJ := ggPZ_eq_mul_core hXp hxp hx1 hxN hcomm hJP.2.1 hJq hpJ
    have hAX_le_AJ : ggAutomizer (ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J) Bs ≤
        ggAutomizer J Bs :=
      ggPZ_automizer_le_of_eq_mul hBstar.2.1 hBsNX hJX hJq hpJ hZ hYJ hDBs hDcent hED
    obtain ⟨f', hf'⟩ := ggPZ_automizer_extend hBstar.2.1.1 hDBs hDcent hint hprod
      (MonoidHom.id (MulAut ↥(Bs ⊓ J))) (by
        rw [MonoidHom.range_eq_map, Subgroup.map_id]
        exact le_top)
    have h9EJ : Nat.card ↥(Bs ⊓ J) ∣ 9 := by
      rw [hcardEJ]
    have hAutJ_dvd_48 : Nat.card (ggAutomizer J Bs) ∣ 48 := by
      have h1 : Nat.card (ggAutomizer J Bs) ∣ Nat.card (MulAut ↥(Bs ⊓ J)) :=
        (Subgroup.card_dvd_of_le hf').trans (Subgroup.card_range_dvd f')
      exact h1.trans (CFSG.GH74.GLS.Stage4.Q9.card_mulAut_dvd_48 (X := ↥(Bs ⊓ J)) h9EJ)
    have hAX_dvd_48 : Nat.card
        (ggAutomizer (ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J) Bs) ∣ 48 :=
      (Subgroup.card_dvd_of_le hAX_le_AJ).trans hAutJ_dvd_48
    exact fun h9 => absurd (h9.trans hAX_dvd_48) (by norm_num)

theorem ggBTwoLineJDatum_of_basis
    {G : Type} [Group G] {Bs J : Subgroup G} [Fact (Nat.Prime 3)]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (h : Module.Basis (Fin 4) (ZMod 3) V)
    (φ : Fin 4 → MulAut ↥Bs) (α : Fin 4 → Module.Dual (ZMod 3) V)
    (hα : ∀ i j, α i (h j) = b2Pairing j i)
    (hφ : ∀ k v, ggLin (p := 3) ι (φ k) v = v - α k v • h k)
    (hrefl : ∀ k, GGIsReflection 3 (φ k))
    (hAJ : ggAutomizer J Bs = Subgroup.closure ({φ 0, φ 1} : Set (MulAut ↥Bs))) :
    GGResLineJDatum 3 Bs J .B2 := by
  let to4 : Fin 2 → Fin 4 := fun i => ⟨i.1, by omega⟩
  let θ : Fin 2 → MulAut ↥Bs := fun i => φ (to4 (Fin.rev i))
  let hv : Fin 2 → V := fun i => h (to4 (Fin.rev i))
  let hαv : Fin 2 → Module.Dual (ZMod 3) V := fun i => α (to4 (Fin.rev i))
  have hinj : Function.Injective (fun i : Fin 2 => to4 (Fin.rev i)) := by
    intro a b hab
    exact Fin.rev_injective (Fin.ext (by simpa [to4] using congrArg Fin.val hab))
  have hrange : Set.range θ = ({φ 0, φ 1} : Set (MulAut ↥Bs)) := by
    ext ψ
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [θ, to4, Fin.rev]
    · intro hψ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
      rcases hψ with rfl | rfl
      · exact ⟨1, by simp [θ, to4, Fin.rev]⟩
      · exact ⟨0, by simp [θ, to4, Fin.rev]⟩
  have hcartθ : ∀ i j : Fin 2,
      hαv i (hv j) = (GGResLineJType.cartan .B2 i j : ZMod 3) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [hαv, hv, to4, Fin.rev, hα, b2Pairing, GGResLineJType.cartan,
        CartanMatrix.B_two]
  exact ⟨V, inferInstance, inferInstance, ι, θ, hv, hαv,
    (fun j w => hφ (to4 (Fin.rev j)) w),
    (fun j => hrefl (to4 (Fin.rev j))),
    hcartθ,
    (h.linearIndependent.comp (fun i : Fin 2 => to4 (Fin.rev i)) hinj),
    (by rw [hAJ, ← hrange]; rfl)⟩

set_option maxRecDepth 4096 in
theorem ggBTwoPumpEndpoint_contradiction
    {G : Type} [Group G] [Finite G]
    (hLB : GGLBalanceInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hPL : ∀ (z : G) (X : Subgroup G), GGNbr 3 B x D J z X → J ≤ X →
      ¬ 9 ∣ Nat.card (ggAutomizer X Bs))
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hLD : GGResLeviDatum 3 Bs L J K ggSelI (ggTypRankLt 8))
    (hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥J))
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (h : Module.Basis (Fin 4) (ZMod 3) V)
    (φ : Fin 4 → MulAut ↥Bs) (α : Fin 4 → Module.Dual (ZMod 3) V)
    (hα : ∀ i j, α i (h j) = b2Pairing j i)
    (hφ : ∀ k v, ggLin (p := 3) ι (φ k) v = v - α k v • h k)
    (hrefl : ∀ k, GGIsReflection 3 (φ k))
    (hAL : ggAutomizer L Bs = Subgroup.closure ({φ 0, φ 1, φ 2} : Set (MulAut ↥Bs)))
    (hAK : ggAutomizer K Bs = Subgroup.closure ({φ 0, φ 1, φ 3} : Set (MulAut ↥Bs)))
    (hAJ : ggAutomizer J Bs = Subgroup.closure ({φ 0, φ 1} : Set (MulAut ↥Bs))) :
    False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCfg : GGConfig 3 B Bs x L D J := hH.1
  have hBstar : GGBstar 3 B Bs := hCfg.2.1
  have hI : GGThmIHyp 3 B x L := hCfg.1
  have hS : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hInn : GGInnerDiagOn Bs L := hH.2.2.1.1
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) := ggR4_normalizes_J hCfg hInn
  have hcardV : Nat.card V = 3 ^ 4 := by
    calc Nat.card V = Nat.card (Fin 4 → ZMod 3) := Nat.card_congr h.equivFun.toEquiv
      _ = 3 ^ 4 := by simp
  have hcardBs : Nat.card ↥Bs = 81 := by
    have hcardBsV : Nat.card ↥Bs = Nat.card V :=
      Nat.card_congr (Additive.ofMul.trans ι.toEquiv)
    rw [hcardBsV, hcardV]
    norm_num
  let to4 : Fin 2 → Fin 4 := fun i => ⟨i.1, by omega⟩
  have hJT : GGResLineJDatum 3 Bs J .B2 :=
    ggBTwoLineJDatum_of_basis ι h φ α hα hφ hrefl hAJ

  have hcard9 : 9 ≤ Nat.card (Bs ⊓ J : Subgroup G) :=
    ggBTwoCard_le_of_lineDatum hBsJ hJT
  have hJcomp0 : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hH.1.2.2.1.2.2.2.2.2.1
  have hJq : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).1
      hJcomp0.2.2
  let zV : V := h.equivFun.symm b2ZVec
  let z : ↥Bs := Additive.toMul (ι.symm zV)
  have hzι : ι (Additive.ofMul z) = zV := by simp [z]
  have hzrepr_fun : ⇑(h.repr zV) = b2ZVec := by
    rw [← Module.Basis.equivFun_apply]
    ext i
    simp [zV, Module.Basis.equivFun_symm_apply, Finsupp.single_apply]
  have hαz0 : α 0 zV = 0 := by
    change α 0 (h.equivFun.symm b2ZVec) = 0
    rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_four]
    norm_num [b2ZVec, b2Pairing, hα]
  have hαz1 : α 1 zV = 0 := by
    change α 1 (h.equivFun.symm b2ZVec) = 0
    rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_four]
    norm_num [b2ZVec, b2Pairing, hα]
    exact ZMod.natCast_self 3
  have hαz2 : α 2 zV ≠ 0 := by
    change α 2 (h.equivFun.symm b2ZVec) ≠ 0
    rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_four]
    norm_num [b2ZVec, b2Pairing, hα]
    exact fun h0 => (by norm_num : ¬ 3 ∣ 5) ((ZMod.natCast_eq_zero_iff 5 3).mp h0)
  have hxBs : x ∈ Bs := hBstar.1 hS.2.1
  let xV : V := ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))
  have hαix : ∀ i : Fin 3, α (Fin.castSucc i) xV = 0 := by
    intro i
    have hφi : φ (Fin.castSucc i) ∈ ggAutomizer L Bs := by
      rw [hAL]
      fin_cases i <;> exact Subgroup.subset_closure (by simp)
    have hfix : φ (Fin.castSucc i) (⟨x, hxBs⟩ : ↥Bs) = ⟨x, hxBs⟩ :=
      ggResI_automizer_fix hxBs hS.2.2.2.1.1 _ hφi
    have hlin : ggLin (p := 3) ι (φ (Fin.castSucc i)) xV = xV :=
      (ggLin_fix_iff (p := 3) ι (φ (Fin.castSucc i)) (⟨x, hxBs⟩ : ↥Bs)).mp hfix
    have hv := hφ (Fin.castSucc i) xV
    rw [hlin] at hv
    have hzero : (α (Fin.castSucc i)) xV • h (Fin.castSucc i) = 0 :=
      sub_eq_self.mp hv.symm
    exact (smul_eq_zero.mp hzero).resolve_right (h.ne_zero (Fin.castSucc i))
  have hα2x : α 2 xV = 0 := by simpa using hαix 2
  let φo : Option (Fin 3) → MulAut ↥Bs
    | none => φ 3
    | some i => φ (Fin.castSucc i)
  let ho : Option (Fin 3) → V
    | none => h 3
    | some i => h (Fin.castSucc i)
  let αo : Option (Fin 3) → Module.Dual (ZMod 3) V
    | none => α 3
    | some i => α (Fin.castSucc i)
  have hφo : ∀ o w, ggLin (p := 3) ι (φo o) w = w - αo o w • ho o := by
    intro o w
    cases o with
    | none => simpa [φo, αo, ho] using hφ 3 w
    | some i => simpa [φo, αo, ho] using hφ (Fin.castSucc i) w
  have hro : ∀ j : Fin 3, j ≠ 2 → GGIsReflection 3 (φo (some j)) := by
    intro j _; simpa [φo] using hrefl (Fin.castSucc j)
  have hdim : Module.finrank (ZMod 3) V = Fintype.card (Fin 3) + 1 := by
    rw [Module.finrank_eq_card_basis h]
    norm_num
  have hind2 : LinearIndependent (ZMod 3) (fun i : Fin 2 => α (to4 i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hdet : (Matrix.of fun j i : Fin 2 => α (to4 i) (h (to4 j))).det ≠ 0 := by
      rw [show (Matrix.of fun j i : Fin 2 => α (to4 i) (h (to4 j))) =
          Matrix.of (fun j i : Fin 2 => b2Pairing (to4 j) (to4 i)) by
        ext j i
        exact hα (to4 i) (to4 j)]
      rw [Matrix.det_fin_two]
      norm_num [to4, b2Pairing]
      exact fun h0 => (by norm_num : ¬ 3 ∣ 2) ((ZMod.natCast_eq_zero_iff 2 3).mp h0)
    have hv : Matrix.mulVec (Matrix.of fun j i : Fin 2 => α (to4 i) (h (to4 j))) g = 0 := by
      ext j
      have h1 := congrArg (fun f : Module.Dual (ZMod 3) V => f (h (to4 j))) hg
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        LinearMap.zero_apply] at h1
      simpa [Matrix.mulVec, dotProduct, Matrix.of_apply, mul_comm] using h1
    exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hv) i
  have hj01 : ∀ j : {i : Fin 3 // i ≠ 2}, j.1 = 0 ∨ j.1 = 1 := by
    intro j
    have hlt : j.1.val < 3 := j.1.isLt
    have hne : j.1.val ≠ 2 := fun h => j.2 (Fin.ext h)
    have h : j.1.val = 0 ∨ j.1.val = 1 := by omega
    rcases h with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hindJo : LinearIndependent (ZMod 3)
      (fun j : {i : Fin 3 // i ≠ 2} => αo (some j.1)) := by
    let j0 : {i : Fin 3 // i ≠ 2} := ⟨0, by norm_num⟩
    let j1 : {i : Fin 3 // i ≠ 2} := ⟨1, by norm_num⟩
    have hbij : Function.Bijective ![j0, j1] := by
      constructor
      · intro k l hkl
        fin_cases k <;> fin_cases l <;> simp [j0, j1] at hkl ⊢
      · intro j
        rcases hj01 j with h | h
        · refine ⟨0, ?_⟩
          rw [show j = j0 from Subtype.ext h]
          rfl
        · refine ⟨1, ?_⟩
          rw [show j = j1 from Subtype.ext h]
          rfl
    let e : Fin 2 ≃ {i : Fin 3 // i ≠ 2} := Equiv.ofBijective ![j0, j1] hbij
    have he0 : e 0 = j0 := rfl
    have he1 : e 1 = j1 := rfl
    rw [Fintype.linearIndependent_iff]
    intro g hg
    let g2 : Fin 2 → ZMod 3 := fun i => if i = 0 then g j0 else g j1
    have hg2sum : ∑ i : Fin 2, g2 i • α (to4 i) = 0 := by
      have h1 := hg
      rw [← Equiv.sum_comp e, Fin.sum_univ_two, he0, he1] at h1
      simpa [g2, αo, j0, j1, to4, Fin.castSucc] using h1
    have hg2 : ∀ i : Fin 2, g2 i = 0 := (Fintype.linearIndependent_iff.mp hind2) g2 hg2sum
    have hcov : ∀ j : {i : Fin 3 // i ≠ 2}, j = e 0 ∨ j = e 1 := by
      intro j
      rcases hj01 j with h | h
      · left
        rw [he0]
        exact Subtype.ext h
      · right
        rw [he1]
        exact Subtype.ext h
    intro j
    rcases hcov j with h | h
    · rw [h, he0]
      simpa [g2] using hg2 0
    · rw [h, he1]
      simpa [g2] using hg2 1
  have hJo : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {i : Fin 3 // i ≠ 2} => φo (some j.1)) := by
    have hrange : Set.range (fun j : {i : Fin 3 // i ≠ 2} => φo (some j.1)) =
        ({φ 0, φ 1} : Set (MulAut ↥Bs)) := by
      ext ψ
      constructor
      · rintro ⟨j, rfl⟩
        rcases hj01 j with h | h
        · have hj : j = ⟨0, by norm_num⟩ := Subtype.ext h
          rw [hj]; simp [φo]
        · have hj : j = ⟨1, by norm_num⟩ := Subtype.ext h
          rw [hj]; simp [φo]
      · intro hψ
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
        rcases hψ with rfl | rfl
        · exact ⟨⟨0, by norm_num⟩, by simp [φo]⟩
        · exact ⟨⟨1, by norm_num⟩, by simp [φo]⟩
    rw [hAJ, ← hrange]
  have hzroot : ∀ j : Fin 3, j ≠ 2 → αo (some j) (ι (Additive.ofMul z)) = 0 := by
    intro j hj
    have hj01 : j = 0 ∨ j = 1 := by
      fin_cases j
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hj
    rcases hj01 with rfl | rfl
    · rw [hzι]; simpa [αo] using hαz0
    · rw [hzι]; simpa [αo] using hαz1
  have hDz : (z : G) ∈ D :=
    (ggResI_fixJ_le_D hH ι hφo hro hdim hJo hindJo).1 z hzroot
  have hzx : (z : G) ∉ Subgroup.zpowers x := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hzBs : z = (⟨x, hxBs⟩ : ↥Bs) ^ k := by
      apply Subtype.ext
      simpa [Subgroup.coe_zpow] using hk.symm
    have hzVk : zV = k • xV := by
      calc zV = ι (Additive.ofMul z) := hzι.symm
        _ = ι (Additive.ofMul ((⟨x, hxBs⟩ : ↥Bs) ^ k)) := by rw [hzBs]
        _ = ι (k • Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) := by rw [ofMul_zpow]
        _ = k • xV := by rw [map_zsmul]
    have hzero : α 2 zV = 0 := by
      rw [hzVk, map_zsmul, hα2x, smul_zero]
    exact hαz2 hzero
  obtain ⟨hXp, hJX, hBsNX, hnot9⟩ :=
    ggBTwoPumpEndpoint_order_bound hLB hPL hH hLD hJT hcardBs hZ hDz hzx
  have hBsElem : IsElemAbelian 3 Bs := hBstar.2.1
  have hcard9' : 3 ^ 2 ≤ Nat.card (Bs ⊓ J : Subgroup G) := by simpa using hcard9
  have hφ0L : φ 0 ∈ ggAutomizer L Bs := by
    rw [hAL]; exact Subgroup.subset_closure (by simp)
  have hφ1L : φ 1 ∈ ggAutomizer L Bs := by
    rw [hAL]; exact Subgroup.subset_closure (by simp)
  have hφ2L : φ 2 ∈ ggAutomizer L Bs := by
    rw [hAL]; exact Subgroup.subset_closure (by simp)
  have hφ3K : φ 3 ∈ ggAutomizer K Bs := by
    rw [hAK]; exact Subgroup.subset_closure (by simp)
  have hφ0K : φ 0 ∈ ggAutomizer K Bs := by
    rw [hAK]; exact Subgroup.subset_closure (by simp)
  have hφ1K : φ 1 ∈ ggAutomizer K Bs := by
    rw [hAK]; exact Subgroup.subset_closure (by simp)
  have hφ0top : φ 0 ∈ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top hφ0L
  have hφ1top : φ 1 ∈ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top hφ1L
  have hφ2top : φ 2 ∈ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top hφ2L
  have hφ3top : φ 3 ∈ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top hφ3K
  have hinv0 : (φ 0)⁻¹ = φ 0 := inv_eq_of_mul_eq_one_right (hrefl 0).1
  have hinv1 : (φ 1)⁻¹ = φ 1 := inv_eq_of_mul_eq_one_right (hrefl 1).1
  have hinv2 : (φ 2)⁻¹ = φ 2 := inv_eq_of_mul_eq_one_right (hrefl 2).1
  have hinv3 : (φ 3)⁻¹ = φ 3 := inv_eq_of_mul_eq_one_right (hrefl 3).1
  have htAtop : b2TA φ ∈ ggAutomizer ⊤ Bs := by
    simp only [b2TA]
    exact mul_mem (mul_mem hφ3top hφ2top) hφ3top
  have htBtop : b2TB φ ∈ ggAutomizer ⊤ Bs := by
    simp only [b2TB]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hφ2top hφ0top) hφ1top)
      hφ3top) hφ1top) hφ0top) hφ2top
  have htArefl : GGIsReflection 3 (b2TA φ) := by
    have heq : b2TA φ = φ 3 * φ 2 * (φ 3)⁻¹ := by simp [b2TA, hinv3]
    rw [heq]
    exact (hrefl 2).conj' (φ 3)
  have htBrefl : GGIsReflection 3 (b2TB φ) := by
    let w : MulAut ↥Bs := φ 2 * φ 0 * φ 1
    have hwinv : w⁻¹ = φ 1 * φ 0 * φ 2 := by
      change (φ 2 * φ 0 * φ 1)⁻¹ = φ 1 * φ 0 * φ 2
      rw [mul_inv_rev, mul_inv_rev, hinv0, hinv1, hinv2]
      group
    have heq : b2TB φ = w * φ 3 * w⁻¹ := by
      rw [hwinv]
      simp [b2TB, w, mul_assoc]
    rw [heq]
    exact (hrefl 3).conj' w
  have hR : ∀ k : Fin 4,
      LinearMap.toMatrix h h (ggLin (p := 3) ι (φ k)).toLinearMap = b2ReflMat k :=
    fun k => toMatrix_of_b2_reflection h α (fun k => ggLin (p := 3) ι (φ k)) hα
      (fun k v => hφ k v) k
  have hmatA : LinearMap.toMatrix h h (ggLin (p := 3) ι (b2TA φ)).toLinearMap =
      b2TAMat b2ReflMat := by
    have heq : ggLin (p := 3) ι (b2TA φ) =
        b2TA (fun k => ggLin (p := 3) ι (φ k)) := by
      rw [b2TA]
      repeat rw [map_mul]
      rfl
    rw [heq]
    exact toMatrix_b2TA h (fun k => ggLin (p := 3) ι (φ k)) hR
  let rB : Fin 4 → V ≃ₗ[ZMod 3] V := fun k => ggLin (p := 3) ι (φ k)
  have hRB : ∀ k, LinearMap.toMatrix h h (rB k).toLinearMap = b2ReflMat k := hR
  have hmatB' : LinearMap.toMatrix h h (b2TB rB).toLinearMap =
      b2TBMat b2ReflMat := toMatrix_b2TB h rB hRB
  have hmatB : LinearMap.toMatrix h h (ggLin (p := 3) ι (b2TB φ)).toLinearMap =
      b2TBMat b2ReflMat := by
    have heq : ggLin (p := 3) ι (b2TB φ) = b2TB rB := by
      rw [b2TB]
      repeat rw [map_mul]
      rfl
    rw [← heq] at hmatB'
    exact hmatB'
  have hfixVA : ggLin (p := 3) ι (b2TA φ) zV = zV := by
    apply h.repr.injective
    apply Finsupp.ext
    intro i
    have hfun : ⇑(h.repr ((ggLin (p := 3) ι (b2TA φ)).toLinearMap zV)) = ⇑(h.repr zV) := by
      rw [← LinearMap.toMatrix_mulVec_repr h h (ggLin (p := 3) ι (b2TA φ)).toLinearMap zV]
      rw [hmatA, hzrepr_fun, b2TAMat_mulVec_z]
    simpa using congrFun hfun i
  have hfixVB : ggLin (p := 3) ι (b2TB φ) zV = zV := by
    apply h.repr.injective
    apply Finsupp.ext
    intro i
    have hfun : ⇑(h.repr ((ggLin (p := 3) ι (b2TB φ)).toLinearMap zV)) = ⇑(h.repr zV) := by
      rw [← LinearMap.toMatrix_mulVec_repr h h (ggLin (p := 3) ι (b2TB φ)).toLinearMap zV]
      rw [hmatB, hzrepr_fun, b2TBMat_mulVec_z]
    simpa using congrFun hfun i
  have htzA : b2TA φ z = z :=
    (ggLin_fix_iff (p := 3) ι (b2TA φ) z).mpr (by rw [hzι]; exact hfixVA)
  have htzB : b2TB φ z = z :=
    (ggLin_fix_iff (p := 3) ι (b2TB φ) z).mpr (by rw [hzι]; exact hfixVB)
  have htAnorm : b2TA φ ∈ Subgroup.normalizer (ggAutomizer
      (ggLayerClosure 3 (Subgroup.centralizer ({(z : G)} : Set G)) J) Bs :
        Set (MulAut ↥Bs)) :=
    ggAutomizer_mem_normalizer_of_fixed_reflection hBsElem hXp hJX hJq hZ hcard9' htAtop
      htArefl htzA
  have htBnorm : b2TB φ ∈ Subgroup.normalizer (ggAutomizer
      (ggLayerClosure 3 (Subgroup.centralizer ({(z : G)} : Set G)) J) Bs :
        Set (MulAut ↥Bs)) :=
    ggAutomizer_mem_normalizer_of_fixed_reflection hBsElem hXp hJX hJq hZ hcard9' htBtop
      htBrefl htzB
  have hφ0J : φ 0 ∈ ggAutomizer J Bs := by
    rw [hAJ]; exact Subgroup.subset_closure (by simp)
  have hφ1J : φ 1 ∈ ggAutomizer J Bs := by
    rw [hAJ]; exact Subgroup.subset_closure (by simp)
  have hφ0X : φ 0 ∈ ggAutomizer
      (ggLayerClosure 3 (Subgroup.centralizer ({(z : G)} : Set G)) J) Bs :=
    ggAutomizer_mono Bs hJX hφ0J
  have hφ1X : φ 1 ∈ ggAutomizer
      (ggLayerClosure 3 (Subgroup.centralizer ({(z : G)} : Set G)) J) Bs :=
    ggAutomizer_mono Bs hJX hφ1J
  have hforced : 9 ∣ Nat.card (ggAutomizer
      (ggLayerClosure 3 (Subgroup.centralizer ({(z : G)} : Set G)) J) Bs) :=
    qTwoBTwoForced_nine_dvd_mulAut (E := ↥Bs) ι h α φ hφ hα
      (ggAutomizer (ggLayerClosure 3 (Subgroup.centralizer ({(z : G)} : Set G)) J) Bs)
      hφ0X hφ1X htAnorm htBnorm
  exact hnot9 hforced

private def b2Idx {Λ : Type} (e : Fin 3 ≃ Λ) : Fin 4 → Option Λ :=
  ![some (e 1), some (e 2), some (e 0), none]

private theorem b2Idx_injective {Λ : Type} (e : Fin 3 ≃ Λ) :
    Function.Injective (b2Idx e) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp [b2Idx, e.injective.eq_iff] at hab ⊢

private theorem b2Idx_surjective {Λ : Type} (e : Fin 3 ≃ Λ) :
    Function.Surjective (b2Idx e) := by
  intro o
  cases o with
  | none => exact ⟨3, by simp [b2Idx]⟩
  | some i =>
      obtain ⟨j, rfl⟩ := e.surjective i
      fin_cases j
      · exact ⟨2, by simp [b2Idx]⟩
      · exact ⟨0, by simp [b2Idx]⟩
      · exact ⟨1, by simp [b2Idx]⟩

private theorem b2Idx_eq_carrierPoint {Λ : Type} (e : Fin 3 ≃ Λ) :
    b2Idx e = ggResQTwoCarrierPoint e 0 := by
  funext k
  fin_cases k
  · change some (e 1) = ggResIIIdx e (1 : Fin 3).castSucc
    rw [ggResIIIdx_castSucc]
  · change some (e 2) = ggResIIIdx e (2 : Fin 3).castSucc
    rw [ggResIIIdx_castSucc]
  · change some (e 0) = ggResIIIdx e (0 : Fin 3).castSucc
    rw [ggResIIIdx_castSucc]
  · change none = ggResIIIdx e (Fin.last 3)
    rw [ggResIIIdx_last]

private theorem b2RangeL {G : Type} [Group G] {Bs : Subgroup G} {Λ : Type} [Fintype Λ]
    (e : Fin 3 ≃ Λ) (φ : Option Λ → MulAut ↥Bs) :
    Set.range (fun i : Λ => φ (some i)) =
      ({φ (b2Idx e 0), φ (b2Idx e 1), φ (b2Idx e 2)} : Set (MulAut ↥Bs)) := by
  ext ψ
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    fin_cases j <;> simp [b2Idx]
  · rintro (rfl | rfl | rfl)
    · exact ⟨e 1, by simp [b2Idx]⟩
    · exact ⟨e 2, by simp [b2Idx]⟩
    · exact ⟨e 0, by simp [b2Idx]⟩

private theorem b2RangeK {G : Type} [Group G] {Bs : Subgroup G} {Λ : Type} [Fintype Λ] {b : Λ} (e : Fin 3 ≃ Λ)
    (hib : e 0 = b) (φ : Option Λ → MulAut ↥Bs) :
    Set.range (fun j : {i : Λ // i ≠ b} => φ (some j.1)) ∪ {φ none} =
      ({φ (b2Idx e 0), φ (b2Idx e 1), φ (b2Idx e 3)} : Set (MulAut ↥Bs)) := by
  have h1 : e 1 ≠ b := by
    intro h; have : (1 : Fin 3) = 0 := e.injective (h.trans hib.symm); omega
  have h2 : e 2 ≠ b := by
    intro h; have : (2 : Fin 3) = 0 := e.injective (h.trans hib.symm); omega
  ext ψ
  constructor
  · rintro (⟨j, rfl⟩ | rfl)
    · obtain ⟨i, hi⟩ := e.surjective j.1
      have hi0 : i ≠ 0 := by
        intro h0
        apply j.2
        rw [← hi, h0]
        exact hib
      change φ (some j.1) ∈ ({φ (b2Idx e 0), φ (b2Idx e 1), φ (b2Idx e 3)} :
        Set (MulAut ↥Bs))
      rw [← hi]
      fin_cases i
      · exact absurd rfl hi0
      · simp [b2Idx]
      · simp [b2Idx]
    · simp [b2Idx]
  · rintro (rfl | rfl | rfl)
    · exact Or.inl ⟨⟨e 1, h1⟩, by simp [b2Idx]⟩
    · exact Or.inl ⟨⟨e 2, h2⟩, by simp [b2Idx]⟩
    · exact Or.inr rfl

private theorem b2RangeJ {G : Type} [Group G] {Bs : Subgroup G} {Λ : Type} [Fintype Λ] {b : Λ} (e : Fin 3 ≃ Λ)
    (hib : e 0 = b) (φ : Option Λ → MulAut ↥Bs) :
    Set.range (fun j : {i : Λ // i ≠ b} => φ (some j.1)) =
      ({φ (b2Idx e 0), φ (b2Idx e 1)} : Set (MulAut ↥Bs)) := by
  have h1 : e 1 ≠ b := by
    intro h; have : (1 : Fin 3) = 0 := e.injective (h.trans hib.symm); omega
  have h2 : e 2 ≠ b := by
    intro h; have : (2 : Fin 3) = 0 := e.injective (h.trans hib.symm); omega
  ext ψ
  constructor
  · rintro ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := e.surjective j.1
    have hi0 : i ≠ 0 := by
      intro h0
      apply j.2
      rw [← hi, h0]
      exact hib
    change φ (some j.1) ∈ ({φ (b2Idx e 0), φ (b2Idx e 1)} : Set (MulAut ↥Bs))
    rw [← hi]
    fin_cases i
    · exact absurd rfl hi0
    · simp [b2Idx]
    · simp [b2Idx]
  · rintro (rfl | rfl)
    · exact ⟨⟨e 1, h1⟩, by simp [b2Idx]⟩
    · exact ⟨⟨e 2, h2⟩, by simp [b2Idx]⟩

private theorem b2LI_smul {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {H : Fin 4 → V} (hLI : LinearIndependent (ZMod 3) H)
    {lam : Fin 4 → ZMod 3} (hlam : ∀ i, lam i ≠ 0) :
    LinearIndependent (ZMod 3) (fun i => lam i • H i) := by
  rw [Fintype.linearIndependent_iff] at hLI ⊢
  intro g hg
  have hsum : ∑ i, (g i * lam i) • H i = 0 := by
    simpa [smul_smul, mul_assoc, mul_comm, mul_left_comm] using hg
  have hzero := hLI (fun i => g i * lam i) hsum
  intro i
  exact (mul_eq_zero.mp (hzero i)).resolve_right (hlam i)

private theorem b2Span_smul {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {H : Fin 4 → V} (hspan : Submodule.span (ZMod 3) (Set.range H) = ⊤)
    {lam : Fin 4 → ZMod 3} (hlam : ∀ i, lam i ≠ 0) :
    Submodule.span (ZMod 3) (Set.range (fun i => lam i • H i)) = ⊤ := by
  apply top_le_iff.mp
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have hHi : H i = (lam i)⁻¹ • (lam i • H i) := by
    rw [smul_smul, inv_mul_cancel₀ (hlam i), one_smul]
  rw [hHi]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem GGResQTwoResidualCellTag.lineJDatum_B2
    {G : Type} [Group G] {Bs J : Subgroup G} [Fact (Nat.Prime 3)]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod 3) V}
    {u v : ZMod 3} {tag : GGResQTwoResidual}
    (htag : tag = .B3b0c2 ∨ tag = .C3b0c2)
    (hcell : GGResQTwoResidualCellTag tag b CL CK u v)
    (hφ : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection 3 (φ o))
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod 3))
    (hsel : LinearIndependent (ZMod 3) h)
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b} => φ (some j))) :
    GGResLineJDatum 3 Bs J .B2 := by
  obtain ⟨n, C, ib, ic, e₁, e₂, e, hCe, hib, _hrow, _hcol, _hCKaa, hshape⟩ := hcell
  have hn : n = 3 := ggResQTwoResidualShape_n_eq_three _ _ _ _ _ _ _ _ _ hshape
  subst n
  rw [ggResQTwoResidualShape_three] at hshape
  obtain ⟨hC, hib0, -, -, -, -, -⟩ := hshape
  have hib0zero : ib = 0 := by
    rcases htag with hB3 | hC3
    · subst hB3
      simpa [ggResQTwoResidualData] using hib0
    · subst hC3
      simpa [ggResQTwoResidualData] using hib0
  have he0b : e 0 = b := by simpa [hib0zero] using hib
  let lam : Fin 4 → ZMod 3 :=
    if tag = .B3b0c2 then ![1, -1, 1, -1] else 1
  have hlam : ∀ i, lam i ≠ 0 := by
    rcases htag with rfl | rfl <;> intro i <;> fin_cases i <;> simp [lam]
  let H0 : Fin 4 → V := fun i => h (b2Idx e i)
  let A0 : Fin 4 → Module.Dual (ZMod 3) V := fun i => α (b2Idx e i)
  let P0 : Fin 4 → MulAut ↥Bs := fun i => φ (b2Idx e i)
  let H : Fin 4 → V := fun i => lam i • H0 i
  let A : Fin 4 → Module.Dual (ZMod 3) V := fun i => (lam i)⁻¹ • A0 i
  let f : Fin 2 → Fin 4 := ![1, 0]
  have hfinj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [f] at hab ⊢
  have hLI0 : LinearIndependent (ZMod 3) H0 :=
    hsel.comp (b2Idx e) (b2Idx_injective e)
  have hLI : LinearIndependent (ZMod 3) H := b2LI_smul hLI0 hlam
  have hpair : ∀ i j : Fin 2,
      A (f i) (H (f j)) = (GGResLineJType.cartan .B2 i j : ZMod 3) := by
    intro i j
    rcases htag with rfl | rfl
    · have hC' : C = !![2, -1, 0; -1, 2, -2; 0, -1, 2] := by
        have h1 : C = CartanMatrix.B 3 := by
          simpa [ggResQTwoResidualData] using hC
        rw [h1]
        decide +kernel
      have hz1 : (1 : ZMod 3) = -2 := by
        have h : ((1 : ℤ) : ZMod 3) = ((-2 : ℤ) : ZMod 3) := by
          rw [ZMod.intCast_eq_intCast_iff]
          norm_num
        simpa using h
      have hz2 : (2 : ZMod 3) = -1 := by
        have h : ((2 : ℤ) : ZMod 3) = ((-1 : ℤ) : ZMod 3) := by
          rw [ZMod.intCast_eq_intCast_iff]
          norm_num
        simpa using h
      fin_cases i <;> fin_cases j <;>
        (simp [A, H, A0, H0, f, lam, b2Idx, hL, hCe, hC',
          GGResLineJType.cartan, CartanMatrix.B_two, smul_eq_mul]
         <;> (first | exact hz1 | exact hz2))
    · have hC' : C = !![2, -1, 0; -1, 2, -1; 0, -2, 2] := by
        have h1 : C = CartanMatrix.C 3 := by
          simpa [ggResQTwoResidualData] using hC
        rw [h1]
        decide +kernel
      fin_cases i <;> fin_cases j <;>
        (simp [A, H, A0, H0, f, lam, b2Idx, hL, hCe, hC',
          GGResLineJType.cartan, CartanMatrix.B_two])
  have hform : ∀ i w,
      ggLin (p := 3) ι (P0 (f i)) w = w - A (f i) w • H (f i) := by
    intro i w
    rw [hφ (b2Idx e (f i)) w]
    congr 1
    show A0 (f i) w • H0 (f i) =
      ((lam (f i))⁻¹ • A0 (f i) w) • (lam (f i) • H0 (f i))
    rw [smul_smul, smul_eq_mul]
    have hcoef : (lam (f i))⁻¹ * A0 (f i) w * lam (f i) = A0 (f i) w := by
      rw [mul_assoc, mul_comm (A0 (f i) w) (lam (f i)), ← mul_assoc,
        inv_mul_cancel₀ (hlam (f i)), one_mul]
    rw [hcoef]
  have hrange : Set.range (fun i : Fin 2 => P0 (f i)) =
      ({P0 0, P0 1} : Set (MulAut ↥Bs)) := by
    ext ψ
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [f]
    · rintro (rfl | rfl)
      · exact ⟨1, by simp [f]⟩
      · exact ⟨0, by simp [f]⟩
  have hgen : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : Fin 2 => P0 (f i))) := by
    rw [hrange, hJ, b2RangeJ e he0b φ]
  exact ⟨V, inferInstance, inferInstance, ι, (fun i => P0 (f i)),
    (fun i => H (f i)), (fun i => A (f i)), hform,
    (fun i => hrefl (b2Idx e (f i))), hpair,
    (hLI.comp f hfinj), hgen⟩

theorem ggResQTwoLeviDatumCell_lineJDatum_B2
    {G : Type} [Group G] [Fact (Nat.Prime 3)]
    {Bs L J K : Subgroup G}
    (hD : GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8)
      GGResQTwoResidualCellB2) :
    GGResLineJDatum 3 Bs J .B2 := by
  obtain ⟨Λ, iF, iD, b, ML, CL, MK, CK, V, iAC, iMod, ι, φ, h, α,
    h1, h2, h3, h4, h5, hφ, hrefl, hL, _hK, hselI, hfL, hfK, _hAL, _hAK, _hdel, hJ,
    hcellB2⟩ := hD
  have hsel : LinearIndependent (ZMod 3) h := by simpa [ggSelI] using hselI
  rcases hcellB2 with hcell | hcell
  · exact GGResQTwoResidualCellTag.lineJDatum_B2 (Or.inl rfl) hcell hφ hrefl hL hsel hJ
  · exact GGResQTwoResidualCellTag.lineJDatum_B2 (Or.inr rfl) hcell hφ hrefl hL hsel hJ

private theorem b2ResidualC3_contradiction
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hLB : GGLBalanceInput)
    (hPL : ∀ (z : G) (X : Subgroup G), GGNbr 3 B x D J z X → J ≤ X →
      ¬ 9 ∣ Nat.card (ggAutomizer X Bs))
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hLD : GGResLeviDatum 3 Bs L J K ggSelI (ggTypRankLt 8))
    (hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥J))
    (hFix : GGTBFixInput)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod 3) V}
    (hφ : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection 3 (φ o))
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod 3))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod 3))
    (hsel : LinearIndependent (ZMod 3) h)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b} => φ (some j)))
    {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} {e₁ e₂ : ℤ}
    (e : Fin n ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = C i j) (hib : e ib = b)
    (hrow : ∀ (j : Fin n) (hj : e j ≠ b),
      CK none (some ⟨e j, hj⟩) = if j = ic then e₁ else 0)
    (hcol : ∀ (j : Fin n) (hj : e j ≠ b),
      CK (some ⟨e j, hj⟩) none = if j = ic then e₂ else 0)
    (hCKaa : CK none none = 2)
    (hshape : GGResQTwoResidualShape .C3b0c2 n C ib ic e₁ e₂
      (α none (h (some b))) (α (some b) (h none))) :
    False := by
  have hn : n = 3 := ggResQTwoResidualShape_n_eq_three _ _ _ _ _ _ _ _ _ hshape
  subst n
  rw [ggResQTwoResidualShape_three] at hshape
  obtain ⟨hC, hib0, hic, he1, he2, hu, hv⟩ := hshape
  have hC3 : C = CartanMatrix.C 3 := by simpa [ggResQTwoResidualData] using hC
  have hib0 : ib = 0 := by simpa [ggResQTwoResidualData] using hib0
  have hic2 : ic = 2 := by simpa [ggResQTwoResidualData] using hic
  have he1' : e₁ = -1 := by simpa [ggResQTwoResidualData] using he1
  have he2' : e₂ = -1 := by simpa [ggResQTwoResidualData] using he2
  have hu' : α none (h (some b)) = 1 := by simpa [ggResQTwoResidualData] using hu
  have hv' : α (some b) (h none) = 2 := by simpa [ggResQTwoResidualData] using hv
  have he0b : e 0 = b := by simpa [hib0] using hib
  have hu'' : α none (h (some (e 0))) = 1 := by simpa [he0b] using hu'
  have hv'' : α (some (e 0)) (h none) = 2 := by simpa [he0b] using hv'
  have hne1 : e 1 ≠ b := by
    intro hb
    have h10 : (1 : Fin 3) = 0 := e.injective (hb.trans he0b.symm)
    omega
  have hne2 : e 2 ≠ b := by
    intro hb
    have h20 : (2 : Fin 3) = 0 := e.injective (hb.trans he0b.symm)
    omega
  have hLz : ∀ i j : Fin 3,
      α (some (e i)) (h (some (e j))) =
        (!![2, -1, 0; -1, 2, -1; 0, -2, 2] : Matrix (Fin 3) (Fin 3) (ZMod 3)) i j := by
    intro i j
    rw [hL (e i) (e j), hCe i j, hC3]
    have hC3z : ((CartanMatrix.C 3).map (Int.castRingHom (ZMod 3))) =
        !![2, -1, 0; -1, 2, -1; 0, -2, 2] := by
      decide +kernel
    simpa [Matrix.map_apply] using congrFun (congrFun hC3z i) j
  have hK_none1 : α none (h (some (e 1))) = 0 := by
    have h1 := hK none (some ⟨e 1, hne1⟩)
    rw [hrow 1 hne1] at h1
    simpa [hic2, show (1 : Fin 3) ≠ 2 by decide] using h1
  have hK_none2 : α none (h (some (e 2))) = -1 := by
    have h1 := hK none (some ⟨e 2, hne2⟩)
    rw [hrow 2 hne2] at h1
    simpa [hic2, he1'] using h1
  have hK_1none : α (some (e 1)) (h none) = 0 := by
    have h1 := hK (some ⟨e 1, hne1⟩) none
    rw [hcol 1 hne1] at h1
    simpa [hic2, show (1 : Fin 3) ≠ 2 by decide] using h1
  have hK_2none : α (some (e 2)) (h none) = -1 := by
    have h1 := hK (some ⟨e 2, hne2⟩) none
    rw [hcol 2 hne2] at h1
    simpa [hic2, he2'] using h1
  have hCKaa' : α none (h none) = 2 := by simpa [hCKaa] using hK none none
  let H0 : Fin 4 → V := fun i => h (b2Idx e i)
  let A0 : Fin 4 → Module.Dual (ZMod 3) V := fun i => α (b2Idx e i)
  let P0 : Fin 4 → MulAut ↥Bs := fun i => φ (b2Idx e i)
  have hspanH : Submodule.span (ZMod 3) (Set.range h) = ⊤ :=
    ggResI_span_top hFix hH ι hφ hAL hsel
  let hB : Module.Basis (Fin 4) (ZMod 3) V :=
    ggResQTwoCarrierBasis (e := e) 0 h hsel hspanH
  have hBcoe : ⇑hB = H0 := by
    funext k
    simp [hB, H0, b2Idx_eq_carrierPoint]
  have hb2 : b2Pairing = !![2, -2, -1, 0; -1, 2, 0, -1; -1, 0, 2, 1; 0, -1, 2, 2] := by
    decide +kernel
  have hα : ∀ i j : Fin 4, A0 i (H0 j) = b2Pairing j i := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [A0, H0, b2Idx, hb2, hLz, hK_none1, hK_none2, hK_1none, hK_2none,
        hCKaa', hu'', hv'']
  have hφ0 : ∀ k w, ggLin (p := 3) ι (P0 k) w = w - A0 k w • H0 k :=
    fun k w => hφ (b2Idx e k) w
  have hrefl0 : ∀ k, GGIsReflection 3 (P0 k) := fun k => hrefl (b2Idx e k)
  have hAL0 : ggAutomizer L Bs =
      Subgroup.closure ({P0 0, P0 1, P0 2} : Set (MulAut ↥Bs)) := by
    rw [hAL, b2RangeL e φ]
  have hAK0 : ggAutomizer K Bs =
      Subgroup.closure ({P0 0, P0 1, P0 3} : Set (MulAut ↥Bs)) := by
    rw [hAK, b2RangeK e he0b φ]
  have hAJ0 : ggAutomizer J Bs =
      Subgroup.closure ({P0 0, P0 1} : Set (MulAut ↥Bs)) := by
    rw [hJ, b2RangeJ e he0b φ]
  exact ggBTwoPumpEndpoint_contradiction hLB hPL hH hLD hZ ι hB P0 A0
    (by simpa [hBcoe] using hα)
    (by intro k w; simpa [hBcoe] using hφ0 k w)
    hrefl0 hAL0 hAK0 hAJ0

private theorem b2ResidualB3_contradiction
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hLB : GGLBalanceInput)
    (hPL : ∀ (z : G) (X : Subgroup G), GGNbr 3 B x D J z X → J ≤ X →
      ¬ 9 ∣ Nat.card (ggAutomizer X Bs))
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hLD : GGResLeviDatum 3 Bs L J K ggSelI (ggTypRankLt 8))
    (hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥J))
    (hFix : GGTBFixInput)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod 3) V}
    (hφ : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection 3 (φ o))
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod 3))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod 3))
    (hsel : LinearIndependent (ZMod 3) h)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b} => φ (some j)))
    {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} {e₁ e₂ : ℤ}
    (e : Fin n ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = C i j) (hib : e ib = b)
    (hrow : ∀ (j : Fin n) (hj : e j ≠ b),
      CK none (some ⟨e j, hj⟩) = if j = ic then e₁ else 0)
    (hcol : ∀ (j : Fin n) (hj : e j ≠ b),
      CK (some ⟨e j, hj⟩) none = if j = ic then e₂ else 0)
    (hCKaa : CK none none = 2)
    (hshape : GGResQTwoResidualShape .B3b0c2 n C ib ic e₁ e₂
      (α none (h (some b))) (α (some b) (h none))) :
    False := by
  have hn : n = 3 := ggResQTwoResidualShape_n_eq_three _ _ _ _ _ _ _ _ _ hshape
  subst n
  rw [ggResQTwoResidualShape_three] at hshape
  obtain ⟨hC, hib0, hic, he1, he2, hu, hv⟩ := hshape
  have hB3 : C = CartanMatrix.B 3 := by simpa [ggResQTwoResidualData] using hC
  have hib0 : ib = 0 := by simpa [ggResQTwoResidualData] using hib0
  have hic2 : ic = 2 := by simpa [ggResQTwoResidualData] using hic
  have he1' : e₁ = -1 := by simpa [ggResQTwoResidualData] using he1
  have he2' : e₂ = -1 := by simpa [ggResQTwoResidualData] using he2
  have hu' : α none (h (some b)) = 2 := by simpa [ggResQTwoResidualData] using hu
  have hv' : α (some b) (h none) = 1 := by simpa [ggResQTwoResidualData] using hv
  have he0b : e 0 = b := by simpa [hib0] using hib
  have hu'' : α none (h (some (e 0))) = 2 := by simpa [he0b] using hu'
  have hv'' : α (some (e 0)) (h none) = 1 := by simpa [he0b] using hv'
  have hne1 : e 1 ≠ b := by
    intro hb
    have h10 : (1 : Fin 3) = 0 := e.injective (hb.trans he0b.symm)
    omega
  have hne2 : e 2 ≠ b := by
    intro hb
    have h20 : (2 : Fin 3) = 0 := e.injective (hb.trans he0b.symm)
    omega
  have hLz : ∀ i j : Fin 3,
      α (some (e i)) (h (some (e j))) =
        (!![2, 2, 0; 2, 2, 1; 0, 2, 2] : Matrix (Fin 3) (Fin 3) (ZMod 3)) i j := by
    intro i j
    rw [hL (e i) (e j), hCe i j, hB3]
    have hB3z : ((CartanMatrix.B 3).map (Int.castRingHom (ZMod 3))) =
        !![2, 2, 0; 2, 2, 1; 0, 2, 2] := by
      decide +kernel
    simpa [Matrix.map_apply] using congrFun (congrFun hB3z i) j
  have hK_none1 : α none (h (some (e 1))) = 0 := by
    have h1 := hK none (some ⟨e 1, hne1⟩)
    rw [hrow 1 hne1] at h1
    simpa [hic2, show (1 : Fin 3) ≠ 2 by decide] using h1
  have hK_none2 : α none (h (some (e 2))) = 2 := by
    have h1 := hK none (some ⟨e 2, hne2⟩)
    rw [hrow 2 hne2, hic2, he1'] at h1
    exact h1.trans (by decide : (-1 : ZMod 3) = 2)
  have hK_1none : α (some (e 1)) (h none) = 0 := by
    have h1 := hK (some ⟨e 1, hne1⟩) none
    rw [hcol 1 hne1] at h1
    simpa [hic2, show (1 : Fin 3) ≠ 2 by decide] using h1
  have hK_2none : α (some (e 2)) (h none) = 2 := by
    have h1 := hK (some ⟨e 2, hne2⟩) none
    rw [hcol 2 hne2, hic2, he2'] at h1
    exact h1.trans (by decide : (-1 : ZMod 3) = 2)
  have hCKaa' : α none (h none) = 2 := by simpa [hCKaa] using hK none none
  let lam : Fin 4 → ZMod 3 := ![1, -1, 1, -1]
  have hlam : ∀ i, lam i ≠ 0 := by
    intro i
    fin_cases i <;> simp [lam]
  let H0 : Fin 4 → V := fun i => h (b2Idx e i)
  let A0 : Fin 4 → Module.Dual (ZMod 3) V := fun i => α (b2Idx e i)
  let P0 : Fin 4 → MulAut ↥Bs := fun i => φ (b2Idx e i)
  let H : Fin 4 → V := fun i => lam i • H0 i
  let A : Fin 4 → Module.Dual (ZMod 3) V := fun i => (lam i)⁻¹ • A0 i
  have hLI0 : LinearIndependent (ZMod 3) H0 :=
    hsel.comp (b2Idx e) (b2Idx_injective e)
  have hspanH : Submodule.span (ZMod 3) (Set.range h) = ⊤ :=
    ggResI_span_top hFix hH ι hφ hAL hsel
  have hrangeH0 : Set.range H0 = Set.range h := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨b2Idx e i, rfl⟩
    · rintro ⟨o, rfl⟩
      obtain ⟨i, hi⟩ := b2Idx_surjective e o
      exact ⟨i, by simp [H0, hi]⟩
  have hspan0 : Submodule.span (ZMod 3) (Set.range H0) = ⊤ := by
    rw [hrangeH0, hspanH]
  have hLI : LinearIndependent (ZMod 3) H := b2LI_smul hLI0 hlam
  have hspan : Submodule.span (ZMod 3) (Set.range H) = ⊤ :=
    b2Span_smul hspan0 hlam
  have hcard : Fintype.card (Fin 4) = Module.finrank (ZMod 3) V := by
    rw [← finrank_top (ZMod 3) V, ← hspan, finrank_span_eq_card hLI]
  let hB : Module.Basis (Fin 4) (ZMod 3) V :=
    basisOfLinearIndependentOfCardEqFinrank hLI hcard
  have hBcoe : ⇑hB = H :=
    coe_basisOfLinearIndependentOfCardEqFinrank hLI hcard
  have hb2 : b2Pairing = !![2, 1, 2, 0; 2, 2, 0, 2; 2, 0, 2, 1; 0, 2, 2, 2] := by
    decide +kernel
  have hα : ∀ i j : Fin 4, A i (H j) = b2Pairing j i := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      (simp [A, H, A0, H0, lam, b2Idx, hb2, hLz, hK_none1, hK_none2, hK_1none,
        hK_2none, hCKaa', hu'', hv'']
       try decide)
  have hφ0 : ∀ k w, ggLin (p := 3) ι (P0 k) w = w - A k w • H k := by
    intro k w
    rw [hφ (b2Idx e k) w]
    congr 1
    show A0 k w • H0 k = ((lam k)⁻¹ • A0 k w) • (lam k • H0 k)
    rw [smul_smul, smul_eq_mul]
    have hcoef : (lam k)⁻¹ * A0 k w * lam k = A0 k w := by
      rw [mul_assoc, mul_comm (A0 k w) (lam k), ← mul_assoc,
        inv_mul_cancel₀ (hlam k), one_mul]
    rw [hcoef]
  have hrefl0 : ∀ k, GGIsReflection 3 (P0 k) := fun k => hrefl (b2Idx e k)
  have hAL0 : ggAutomizer L Bs =
      Subgroup.closure ({P0 0, P0 1, P0 2} : Set (MulAut ↥Bs)) := by
    rw [hAL, b2RangeL e φ]
  have hAK0 : ggAutomizer K Bs =
      Subgroup.closure ({P0 0, P0 1, P0 3} : Set (MulAut ↥Bs)) := by
    rw [hAK, b2RangeK e he0b φ]
  have hAJ0 : ggAutomizer J Bs =
      Subgroup.closure ({P0 0, P0 1} : Set (MulAut ↥Bs)) := by
    rw [hJ, b2RangeJ e he0b φ]
  exact ggBTwoPumpEndpoint_contradiction hLB hPL hH hLD hZ ι hB P0 A
    (by simpa [hBcoe] using hα)
    (by intro k w; simpa [hBcoe] using hφ0 k w)
    hrefl0 hAL0 hAK0 hAJ0
theorem ggResQTwoResidualCellB2_contradiction
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hLB : GGLBalanceInput)
    (hPL : ∀ (z : G) (X : Subgroup G), GGNbr 3 B x D J z X → J ≤ X →
      ¬ 9 ∣ Nat.card (ggAutomizer X Bs))
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8)
      GGResQTwoResidualCellB2)
    (hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥J))
    (hFix : GGTBFixInput) :
    False := by
  classical
  have hLD : GGResLeviDatum 3 Bs L J K ggSelI (ggTypRankLt 8) :=
    GGResLeviDatumCell.toDatum hD
  obtain ⟨Λ, iF, iD, b, ML, CL, MK, CK, V, iAC, iMod, ι, φ, h, α,
    h1, h2, h3, h4, h5, hφ, hrefl, hL, hK, hselI, hfL, hfK, hAL, hAK, hdel, hJ,
    hcellB2⟩ := hD
  have hsel : LinearIndependent (ZMod 3) h := by simpa [ggSelI] using hselI
  rcases hcellB2 with hcell | hcell
  · obtain ⟨n, C, ib, ic, e₁, e₂, e, hCe, hib, hrow, hcol, hCKaa, hshape⟩ := hcell
    exact b2ResidualB3_contradiction hLB hPL hH hLD hZ hFix hφ hrefl hL hK hsel
      hAL hAK hJ e hCe hib hrow hcol hCKaa hshape
  · obtain ⟨n, C, ib, ic, e₁, e₂, e, hCe, hib, hrow, hcol, hCKaa, hshape⟩ := hcell
    exact b2ResidualC3_contradiction hLB hPL hH hLD hZ hFix hφ hrefl hL hK hsel
      hAL hAK hJ e hCe hib hrow hcol hCKaa hshape


theorem ggResQTwoResidualCellTagB2_contradiction
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hLB : GGLBalanceInput)
    (hPL : ∀ (z : G) (X : Subgroup G), GGNbr 3 B x D J z X → J ≤ X →
      ¬ 9 ∣ Nat.card (ggAutomizer X Bs))
    (hH : GGResHyp 3 B Bs x L D J y K)
    {tag : GGResQTwoResidual}
    (htag : tag = .B3b0c2 ∨ tag = .C3b0c2)
    (hD : GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8)
      (GGResQTwoResidualCellTag tag))
    (hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥J))
    (hFix : GGTBFixInput) :
    False := by
  rcases htag with rfl | rfl
  · exact ggResQTwoResidualCellB2_contradiction hLB hPL hH
      (GGResLeviDatumCell.cell_mono (fun {Λ} b CL CK u v h => Or.inl h) hD) hZ hFix
  · exact ggResQTwoResidualCellB2_contradiction hLB hPL hH
      (GGResLeviDatumCell.cell_mono (fun {Λ} b CL CK u v h => Or.inr h) hD) hZ hFix



theorem ggResQTwoBTwoOmegaEndpoint
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {tag : GGResQTwoResidual}
    (hLB : GGLBalanceInput)
    (hRig : GGLabelRigidInput)
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hcardBs : Nat.card Bs = 81)
    (htag : tag = .B3b0c2 ∨ tag = .C3b0c2)
    (hD : GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8)
      (GGResQTwoResidualCellTag tag))
    (hLmark : LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1))
    (hFix : GGTBFixInput) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDB2 : GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8)
      GGResQTwoResidualCellB2 := by
    rcases htag with rfl | rfl
    · exact GGResLeviDatumCell.cell_mono (fun {Λ} b CL CK u v h => Or.inl h) hD
    · exact GGResLeviDatumCell.cell_mono (fun {Λ} b CL CK u v h => Or.inr h) hD
  have hJT : GGResLineJDatum 3 Bs J .B2 := ggResQTwoLeviDatumCell_lineJDatum_B2 hDB2
  have hcard : Nat.card Bs = 3 ^ (GGResLineJType.rank .B2 + 2) := by
    rw [hcardBs]
    norm_num [GGResLineJType.rank]
  have hCfg : GGConfig 3 B Bs x L D J := hH.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hCfg.2.2
  have hBeq : B = Bs := by
    obtain ⟨⟨-, -, -, -, -, hβ, hSstar, -⟩, hBs, -⟩ := hCfg
    have hBcard : Nat.card B = 3 ^ CFSG.Open.twoLocalPrimeRank 3 G := hSstar.1.2.1
    have h4 : 4 ≤ CFSG.Open.twoLocalPrimeRank 3 G := hβ.2.2.2
    apply Subgroup.eq_of_le_of_card_ge hBs.1
    rw [hcardBs, hBcard, show (81 : ℕ) = 3 ^ 4 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) h4
  have hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
    obtain ⟨-, -, -, -, -, -, hDlast⟩ := hDJ.1
    rw [← hBeq, ← hDlast]
  obtain ⟨hJlabel, hZcenter⟩ :=
    ggF4QTwoOmegaEnd_label_J hH.1 hH.2.2.1.1 hH.2.2.2.2.1 hLmark
  have hΛJ : LargeEvenInLambda2 (⟨.A, 3, 1⟩ : LargeEvenLabel) := by
    simp [LargeEvenInLambda2]
  have hJline : ggResLineJLabel .B2 (⟨.A, 3, 1⟩ : LargeEvenLabel) := by
    simp [ggResLineJLabel]
  have hpJ : 3 ∣ Nat.card J := by
    obtain ⟨e⟩ := CFSG.CGT.PushingUpLit.CGT6.nonempty_mulEquiv_alt_eight_of_psl_four_two
      (statedClassicalModel_of_hasLabel_typeA (n := 3) (f := 1) hΛJ hJlabel)
    have hQ : 3 ∣ Nat.card (J ⧸ Subgroup.center J) := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    exact hQ.trans (Subgroup.card_quotient_dvd_card (Subgroup.center J))
  have hPL : ∀ (z : G) (X : Subgroup G), GGNbr 3 B x D J z X → J ≤ X →
      ¬ 9 ∣ Nat.card (ggAutomizer X Bs) := by
    intro z X hnbX hJX
    have hinnX : GGInnerDiagOn Bs X := hH.2.2.1.2 z X hnbX
    obtain ⟨labX, hΛX, hhasX, -⟩ := largeEvenMarking_exists_hasLabel hinnX
    have hreg : GGRegimeAm2 3 (Nat.card Bs) (⟨.A, 3, 1⟩ : LargeEvenLabel) labX := by
      simp [GGRegimeAm2]
    have hhJX : GGHasLabel (⟨.A, 3, 1⟩ : LargeEvenLabel)
        (↥(J.subgroupOf X) ⧸ Subgroup.center ↥(J.subgroupOf X)) :=
      ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJX).symm hJlabel
    obtain ⟨hN, hx, hBasic⟩ :=
      ggTPNBasicB_of_config (p := 3) hCfg hH.2.2.1.1 hinnX hnbX hJX hpJ hLB
    have hcorners : GGTPNCorners 3 (J.subgroupOf X) :=
      ⟨fun hp7 _ => absurd hp7 (by norm_num),
        fun _ _ _ => ggTPNRankJ_of_am2 hRig hΛJ hreg hhJX⟩
    have hDatum : GGTPNDatumB 3 (Nat.card Bs) (fun _ _ => True)
        (ggAutsOf X Bs hN) (ggAutsOf X B (hCfg.2.1.1.trans hN))
        (X.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf X) :=
      ⟨hBasic, hcorners⟩
    obtain ⟨labJ', labX', hΛJ', hΛX', hrow, hhasJX, hhasX'⟩ :=
      ggTablePRow_am2_a3_of_datum hDatum hhJX labX hΛX hhasX
    have hhasJ' : GGHasLabel labJ' (↥J ⧸ Subgroup.center ↥J) :=
      ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJX) hhasJX
    have hJline' : ggResLineJLabel .B2 labJ' :=
      ggResLineJLabel_of_iso hJline
        (hRig (⟨.A, 3, 1⟩ : LargeEvenLabel) labJ' _ hΛJ hΛJ' hJlabel hhasJ')
    have hnotE6 : ¬ (labX'.tag = .twE6 ∧ 3 ∣ 2 ^ labX'.n + 1) := by
      rintro ⟨htag, _hdvd⟩
      rcases ggTablePRow_B2 hJline' hΛX' hrow with hC | hA | htwA | htwD
      · rw [hC] at htag; simp at htag
      · rcases hA with ⟨hAtag, -, -, -⟩; rw [hAtag] at htag; simp at htag
      · rcases htwA with ⟨htwAtag, -, -, -⟩; rw [htwAtag] at htag; simp at htag
      · rw [htwD] at htag; simp at htag
    have h := ggPumpLineThreeInput_of_row hRig hH hJT hcard hI1 hnbX hJX
      hΛJ' hΛX' hrow hnotE6 hJline' hhasJ' hhasX'
    simpa [GGResLineJType.bad] using h
  apply ggResQTwoResidualCellTagB2_contradiction hLB hPL hH htag hD _ hFix
  rw [hZcenter, Subgroup.card_bot]
  norm_num

end CFSG.StandardType

end
