module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitFiveDel
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitNbrB
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitFiveNbr
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitNbrBA
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitLayer
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitTorus
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitXTransA
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCompA2
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlockAux
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary Additive

variable {G : Type} [Group G] [Finite G]

section General

theorem qtwoDU5_mk_mem_pLayer_sup_center {H : Subgroup G} {y : ↥H} {t z : G}
    (ht : t ∈ LargeEvenPLayer 3 H) (htH : t ∈ H) (hzH : z ∈ H)
    (hz : ∀ h ∈ H, h * z = z * h) (hy : (y : G) = t * z) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) y ∈
      CFSG.pLayer (↥H ⧸ CFSG.pPrimeCore 3 ↥H) 3 ⊔
        Subgroup.center (↥H ⧸ CFSG.pPrimeCore 3 ↥H) := by
  have hyeq : y = ⟨t, htH⟩ * ⟨z, hzH⟩ := Subtype.ext hy
  rw [hyeq, map_mul]
  refine Subgroup.mul_mem_sup ?_ ?_
  · apply qtwoDB7_map_pLayer_le (X := ↥H)
    refine Subgroup.mem_map.mpr ⟨⟨t, htH⟩, ?_, rfl⟩
    exact qtwoDB7_le_pLayer (H := H) (J := LargeEvenPLayer 3 H) le_rfl
      (Subgroup.mem_subgroupOf.mpr ht)
  · apply Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _)
    refine Subgroup.mem_map.mpr ⟨⟨z, hzH⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (hz h h.2)

theorem qtwoDU5_center_range_eq_bot {S : Type} [Group S] (hS : Subgroup.center S = ⊥)
    {θ : S →* G} (hθ : Function.Injective θ) {X : Subgroup G} (hX : θ.range = X) :
    Subgroup.center ↥X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hzθ : (z : G) ∈ θ.range := by rw [hX]; exact z.2
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hzθ
  have huc : u ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply hθ
    have hw : θ w ∈ X := by rw [← hX]; exact MonoidHom.mem_range.mpr ⟨w, rfl⟩
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨θ w, hw⟩)
    simp only [Subgroup.coe_mul] at h
    rw [map_mul, map_mul, hu]
    exact h
  rw [hS, Subgroup.mem_bot] at huc
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hu, huc, map_one]
  rfl

theorem qtwoDU5_three_dvd_quot {H J : Subgroup G} (hJH : J ≤ H)
    (hZ : Subgroup.center ↥J = ⊥) (h3 : 3 ∣ Nat.card ↥J) :
    3 ∣ Nat.card (↥(J.subgroupOf H) ⧸ Subgroup.center ↥(J.subgroupOf H)) := by
  let φ : ↥(J.subgroupOf H) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJH
  have hZ' : Subgroup.center ↥(J.subgroupOf H) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hφz : φ z ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨w', rfl⟩ := φ.surjective w
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) w']
    rw [hZ, Subgroup.mem_bot] at hφz
    exact Subgroup.mem_bot.mpr (φ.injective (hφz.trans (map_one φ).symm))
  rw [hZ', Nat.card_congr (QuotientGroup.quotientBot).toEquiv, Nat.card_congr φ.toEquiv]
  exact h3

theorem qtwoDU5_two_others : ∀ a b c : Fin 5, a ≠ b → c ≠ a → c ≠ b →
    ∃ d₁ d₂ : Fin 5, d₁ ≠ d₂ ∧ d₁ ≠ a ∧ d₁ ≠ b ∧ d₁ ≠ c ∧ d₂ ≠ a ∧ d₂ ≠ b ∧ d₂ ≠ c := by
  decide

theorem qtwoDU5_dSign_dPerm_comm {m : ℕ} {a b d₁ d₂ : Fin m} (h1a : d₁ ≠ a) (h1b : d₁ ≠ b)
    (h2a : d₂ ≠ a) (h2b : d₂ ≠ b) :
    dSign m a b * dPerm m (Equiv.swap d₁ d₂) = dPerm m (Equiv.swap d₁ d₂) * dSign m a b := by
  refine (dBasis m).ext' fun i => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, dPerm_apply, dSign_apply, dSign_apply,
    map_smul, dPerm_apply]
  congr 1
  have ha : Equiv.swap d₁ d₂ a = a := Equiv.swap_apply_of_ne_of_ne (Ne.symm h1a) (Ne.symm h2a)
  have hb : Equiv.swap d₁ d₂ b = b := Equiv.swap_apply_of_ne_of_ne (Ne.symm h1b) (Ne.symm h2b)
  simp only [Equiv.swap_apply_eq_iff, ha, hb]

end General


variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

theorem qtwoDU5_exists_del (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hb' : βL (Additive.ofMul b') = Pi.single c 1) :
    ∃ (α : MulAut ↥Bs) (g : G), QTwoUnitDel Bs βL a b c α g b' ∧
      α ∈ ggAutomizerJoin L Bs 𝒦 := by
  obtain ⟨α, hαJ, hα⟩ := hcoords.join_onto (dSign m a b) (qtwoDB20_dSign_mem_dEven m hab)
  obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp (ggAutomizerJoin_le_top L Bs 𝒦 hαJ)
  exact ⟨α, g, ⟨hab, hca, hcb, hα, hgN, hg, hb'⟩, hαJ⟩

theorem qtwoDU5_conj_b' (hdel : QTwoUnitDel Bs βL a b c α g b') :
    g * (b' : G) * g⁻¹ = (b' : G) := by
  have hαb' : α b' = b' := by
    apply Additive.ofMul.injective
    apply βL.injective
    rw [hdel.sign b', hdel.coord]
    exact qtwoDB16_dSign_single hdel.hca hdel.hcb
  rw [← hdel.conj b', hαb']


theorem qtwoDU5_P_rankOne (hcfg : GGQTwoDCfg 3 B Bs x L D J 𝒦 M e)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hbase : QTwoUnitBase 3 B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (Bs : Set G)))) {d₁ d₂ : Fin m}
    (hd : d₁ ≠ d₂) :
    ggRankOne Bs ((ε (Equiv.swap d₁ d₂) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) =
        (coordBlockSU F0 2 1 {d₁, d₂}).map ψ ∧
      Nat.card ↥((coordBlockSU F0 2 1 {d₁, d₂}).map ψ) = 6 := by
  set r : MulAut ↥Bs := ((ε (Equiv.swap d₁ d₂) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) with hr
  have hrA : r ∈ ggAutomizer L Bs := (ε (Equiv.swap d₁ d₂)).2
  have hrC : r ∈ ggCoxRefl M e := by
    refine hcoords.cox false d₁ d₂ hd r (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hrA)
      fun s => ?_
    rw [hr, hcoords.perm]
    simp [dTau]
  obtain ⟨h1, h6⟩ :=
    qtwoDL1_rankOne_of_odd ggLNoncyclicInput_holds hcfg hM hodd (Or.inl rfl) hrA hrC
  have hP : ggRankOneIn L Bs r = (coordBlockSU F0 2 1 {d₁, d₂}).map ψ := by
    rw [hr, hbase.rankOne d₁ d₂ hd, ggSuPairBlock_eq_coordBlockSU]
  refine ⟨h1.trans hP, ?_⟩
  rw [← hP, ← h1]
  exact h6

theorem qtwoDU5_P_conj (hcfg : GGQTwoDCfg 3 B Bs x L D J 𝒦 M e)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hbase : QTwoUnitBase 3 B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (Bs : Set G))))
    (hdel : QTwoUnitDel Bs βL a b c α g b') {d₁ d₂ : Fin m} (hd : d₁ ≠ d₂)
    (h1a : d₁ ≠ a) (h1b : d₁ ≠ b) (h2a : d₂ ≠ a) (h2b : d₂ ≠ b) :
    ((coordBlockSU F0 2 1 {d₁, d₂}).map ψ).map (MulAut.conj g).toMonoidHom =
      (coordBlockSU F0 2 1 {d₁, d₂}).map ψ := by
  obtain ⟨hr, -⟩ := qtwoDU5_P_rankOne hcfg hM hbase hcoords hodd hd
  set r : MulAut ↥Bs := ((ε (Equiv.swap d₁ d₂) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) with hrdef
  have hcomm : α * r = r * α := by
    refine MulEquiv.ext fun s => ?_
    have hc := DFunLike.congr_fun (qtwoDU5_dSign_dPerm_comm h1a h1b h2a h2b)
      (βL (Additive.ofMul s))
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hc
    have h : βL (Additive.ofMul ((α * r) s)) = βL (Additive.ofMul ((r * α) s)) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, hdel.sign, hrdef, hcoords.perm, hcoords.perm,
        hdel.sign]
      exact hc
    exact Additive.ofMul.injective (βL.injective h)
  have hαr : α * r * α⁻¹ = r := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [← hr, ggRankOne_map_conj hdel.conj r, hαr]

theorem qtwoDU5_center_J (hm : m = 5) (hbase : QTwoUnitBase 3 B Bs x L ψ ε) (c : Fin m)
    (g : G) :
    Subgroup.center ↥(qtwoDelJ ψ c) = ⊥ ∧
      Subgroup.center ↥((qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom) = ⊥ := by
  obtain ⟨θ, hθinj, hθrange, hθrange'⟩ := ggQTwoDUnit_J_iso (by omega) hbase c g
  have hZ : Subgroup.center (Su F0 2 1 (m - 1)) = ⊥ :=
    qtwoDU5_center_eq_bot hbase.card_field (by omega) (by omega)
  exact ⟨qtwoDU5_center_range_eq_bot hZ hθinj hθrange,
    qtwoDU5_center_range_eq_bot hZ ((MulAut.conj g).injective.comp hθinj) hθrange'⟩

theorem qtwoDU5_nbr (hBal : GGLBalanceInput)
    (hcfg : GGQTwoDCfg 3 B Bs x L D J 𝒦 M e) (hm : m = 5)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hbase : QTwoUnitBase 3 B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (Bs : Set G))))
    (hdel : QTwoUnitDel Bs βL a b c α g b') (hb'B : (b' : G) ∈ B)
    (hD : D = Subgroup.closure {x, (b' : G)}) (hJ : J = qtwoDelJ ψ c) :
    ∃ N : Subgroup G, GGNbr 3 B x D J b' N ∧ qtwoDelJ ψ c ≤ N ∧
      (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N ∧
      LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N := by
  classical
  have hC : GGConfig 3 B Bs x L D J := hcfg.1.1.1
  subst hD hJ
  have hBsE : CFSG.Open.IsElemAbelian 3 Bs := hbase.hyp.bstar.2.1
  have hca := hdel.hca
  have hcb := hdel.hcb
  set J₁ : Subgroup G := qtwoDelJ ψ c with hJ₁
  set J₂ : Subgroup G := J₁.map (MulAut.conj g).toMonoidHom with hJ₂
  set H : Subgroup G := Subgroup.centralizer ({(b' : G)} : Set G) with hH
  obtain ⟨d₁, d₂, hd, h1a, h1b, h1c, h2a, h2b, h2c⟩ : ∃ d₁ d₂ : Fin m, d₁ ≠ d₂ ∧ d₁ ≠ a ∧
      d₁ ≠ b ∧ d₁ ≠ c ∧ d₂ ≠ a ∧ d₂ ≠ b ∧ d₂ ≠ c := by
    subst hm
    exact qtwoDU5_two_others a b c hdel.hab hdel.hca hdel.hcb
  set P : Subgroup G := (coordBlockSU F0 2 1 {d₁, d₂}).map ψ with hPdef
  have hgb' := qtwoDU5_conj_b' hdel
  have hginv : g⁻¹ * (b' : G) = (b' : G) * g⁻¹ := by
    have h : (b' : G) * g⁻¹ = g⁻¹ * (b' : G) := by
      calc (b' : G) * g⁻¹ = g⁻¹ * (g * (b' : G) * g⁻¹) := by group
        _ = g⁻¹ * (b' : G) := by rw [hgb']
    exact h.symm
  have hxH : x ∈ H := by
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
    exact CFSG.Open.IsElemAbelian.comm hBsE hbase.x_mem b'.2
  have hx'H : g * x * g⁻¹ ∈ H := by
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
    calc (g * x * g⁻¹) * (b' : G) = g * x * (g⁻¹ * (b' : G)) := by group
      _ = g * x * ((b' : G) * g⁻¹) := by rw [hginv]
      _ = g * (x * (b' : G)) * g⁻¹ := by group
      _ = g * ((b' : G) * x) * g⁻¹ := by
            rw [CFSG.Open.IsElemAbelian.comm hBsE hbase.x_mem b'.2]
      _ = (g * (b' : G) * g⁻¹) * (g * x * g⁻¹) := by group
      _ = (b' : G) * (g * x * g⁻¹) := by rw [hgb']
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hbase.x_order] at this
  have hx'3 : (g * x * g⁻¹) ^ 3 = 1 := by
    have hconj : (g * x * g⁻¹) ^ 3 = g * x ^ 3 * g⁻¹ := by
      rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]
    rw [hconj, hx3]
    group
  have hJcomp :=
    ggQTwoDUnit_J_comp hcfg (by omega) hbase hcoords hdel.hca hdel.hcb hdel.sign hdel.conj
      hdel.coord hb'B
  have hlayer := ggQTwoDUnit_layer hBal hcfg (by omega) hbase hcoords hdel.hca hdel.hcb hdel.sign
    hdel.conj hdel.coord hb'B
  have hJJlay : J₁ ⊔ J₂ ≤ LargeEvenPLayer 3 H := sup_le hlayer.1 hlayer.2
  have h3J₁ : 3 ∣ Nat.card ↥J₁ := qtwoDB17_three_dvd_J (by omega) hbase hdel.hca hdel.hcb hdel.hab
  have hcardJ₂ : Nat.card ↥J₂ = Nat.card ↥J₁ :=
    Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  have h3J₂ : 3 ∣ Nat.card ↥J₂ := hcardJ₂ ▸ h3J₁
  obtain ⟨hZ₁, hZ₂⟩ := qtwoDU5_center_J hm hbase c g
  have hJ₁H : J₁ ≤ H := hJcomp.1.1.trans inf_le_left
  have hJ₂H : J₂ ≤ H := hJcomp.2.1.trans inf_le_left
  have hb'H : (b' : G) ∈ H := by
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
  have hb'c : ∀ h ∈ H, h * (b' : G) = (b' : G) * h := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mp hh
  set xB : ↥Bs := ⟨x, hbase.x_mem⟩ with hxB
  have hβx : βL (Additive.ofMul xB) = fun _ => 1 := hcoords.x_coord hbase.x_mem
  have hβx' : βL (Additive.ofMul xB) = (1 : DVec m) := hβx
  have htH : ∀ s : ↥Bs, (s : G) ∈ H := fun s => by
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
    exact CFSG.Open.IsElemAbelian.comm hBsE s.2 b'.2
  have hyN₁ := qtwoDU5_mk_mem_pLayer_sup_center (H := H) (y := ⟨x, hxH⟩)
    (t := ((xB * b'⁻¹ : ↥Bs) : G)) (z := (b' : G))
    (hJJlay (ggQTwoDUnit_torus (by omega) hbase hcoords hdel.hab hdel.hca hdel.hcb hdel.sign
      hdel.norm hdel.conj (xB * b'⁻¹) (by
        rw [ofMul_mul, map_add, ofMul_inv, map_neg, hβx, hdel.coord]
        simp)))
    (htH _) hb'H hb'c (by simp [hxB])
  have hyN₂ := qtwoDU5_mk_mem_pLayer_sup_center (H := H) (y := ⟨g * x * g⁻¹, hx'H⟩)
    (t := ((α xB * b'⁻¹ : ↥Bs) : G)) (z := (b' : G))
    (hJJlay (ggQTwoDUnit_torus (by omega) hbase hcoords hdel.hab hdel.hca hdel.hcb hdel.sign
      hdel.norm hdel.conj (α xB * b'⁻¹) (by
        rw [ofMul_mul, map_add, ofMul_inv, map_neg, hdel.sign, hβx', hdel.coord, Pi.add_apply,
          Pi.neg_apply, qtwoDB17_dSign_one_apply, if_neg (by tauto), Pi.single_eq_same]
        simp)))
    (htH _) hb'H hb'c (by
      change g * x * g⁻¹ = ((α xB : ↥Bs) : G) * (b' : G)⁻¹ * (b' : G)
      rw [hdel.conj xB]
      simp [hxB])
  have hsub : ({d₁, d₂} : Finset (Fin m)) ⊆ Finset.univ.erase c := by
    intro i hi
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ i⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact h1c
    · exact h2c
  have hP₁ : P ≤ J₁ := by
    refine Subgroup.map_mono fun u hu => ?_
    rw [mem_coordBlockSU_iff] at hu ⊢
    intro i j hij
    exact hu i j (by
      rcases hij with h | h
      · exact Or.inl fun hmem => h (hsub hmem)
      · exact Or.inr fun hmem => h (hsub hmem))
  have hP₂ : P ≤ J₂ := by
    have hPc : P.map (MulAut.conj g).toMonoidHom = P :=
      qtwoDU5_P_conj hcfg hM hbase hcoords hodd hdel hd h1a h1b h2a h2b
    calc P = P.map (MulAut.conj g).toMonoidHom := hPc.symm
      _ ≤ J₂ := Subgroup.map_mono hP₁
  have hP6 : Nat.card ↥P = 6 := (qtwoDU5_P_rankOne hcfg hM hbase hcoords hodd hd).2
  have hPJ : ∃ u ∈ P, ∃ v ∈ J₁, u * v ≠ v * u := by
    by_contra hcon
    push Not at hcon
    have hPbot : P = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have hcen : (⟨u, hP₁ hu⟩ : ↥J₁) ∈ Subgroup.center ↥J₁ := by
        rw [Subgroup.mem_center_iff]
        intro v
        exact Subtype.ext (hcon u hu v v.2).symm
      rw [hZ₁, Subgroup.mem_bot] at hcen
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hcen)
    rw [hPbot, Subgroup.card_bot] at hP6
    norm_num at hP6
  have hxN := qtwoDB17_x_mem_normalizer_J₂ hbase hdel
  have hxc : ∃ j ∈ J₂, x * j ≠ j * x := by
    by_contra hcon
    push Not at hcon
    apply qtwoDB17_x_not_mem_centralizer_J₂ (by omega) hbase hcoords hdel
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (hcon j hj).symm
  exact qtwoDU5_ggNbr hC rfl hxH hx'H hx'3 hJcomp.1 hJcomp.2 hlayer.1 hlayer.2
    (qtwoDU5_three_dvd_quot hJ₁H hZ₁ h3J₁) (qtwoDU5_three_dvd_quot hJ₂H hZ₂ h3J₂) hyN₁ hyN₂
    hP₁ hP₂ hPJ h3J₁ h3J₂ hxN hxc

end CFSG.StandardType.QTwo

end
