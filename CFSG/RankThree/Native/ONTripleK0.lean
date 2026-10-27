module

public import CFSG.RankThree.Native.ONTripleCent
public import CFSG.RankThree.Native.ONTripleA6
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.SetAction
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Local3
public meta import CFSG.RankThree.Native.ONTripleCent
public import Certificates.Certificate8136
public import Certificates.Certificate8139
public import Certificates.Certificate8142
public import Certificates.Certificate8143
public import Certificates.Certificate8144
public import Certificates.Certificate2212
public import Certificates.Certificate2217
public import Certificates.Certificate3171
public import Certificates.Certificate9127
public import Certificates.Certificate9217
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public noncomputable section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.ONSchreier CFSG.ONSchreier.Native Subgroup
open CFSG.RankThree.PartTwo.Sec4.Sporadic.SetAction Equiv
open CFSG.KC.Misc.F7

attribute [local irreducible] dotProduct

@[expose] def blockF (i : Fin 6) : Finset Sub7 :=
  (Finset.range 10).image fun d => pt (10 * i.val + d)

theorem mem_blockF {i : Fin 6} {U : Sub7} :
    U ∈ blockF i ↔ ∃ d < 10, pt (10 * i.val + d) = U := by
  rw [blockF, Finset.mem_image]
  simp only [Finset.mem_range]

theorem pt_mem_blockF {t : ℕ} (ht : t < 60) {i : Fin 6} :
    pt t ∈ blockF i ↔ t / 10 = i.val := by
  rw [mem_blockF]
  constructor
  · rintro ⟨d, hd, e⟩
    by_contra hne
    exact pts_ne _ (by omega) t ht (by omega) e
  · intro h
    exact ⟨t % 10, Nat.mod_lt _ (by norm_num), by congr 1; omega⟩

theorem card_blockF (i : Fin 6) : (blockF i).card = 10 := by
  have hinj : Set.InjOn (fun d => pt (10 * i.val + d)) (Finset.range 10 : Set ℕ) := by
    intro d hd d' hd' e
    rw [Finset.coe_range, Set.mem_Iio] at hd hd'
    by_contra hne
    exact pts_ne _ (by omega) _ (by omega) (by omega) e
  rw [blockF, Finset.card_image_of_injOn hinj, Finset.card_range]

theorem blockF_injective : Function.Injective blockF := by
  intro i j hij
  have h1 : pt (10 * i.val) ∈ blockF i := (pt_mem_blockF (by omega)).2 (by omega)
  rw [hij, pt_mem_blockF (by omega)] at h1
  exact Fin.ext (by omega)

abbrev rhoM : GM →* Equiv.Perm Sub7 := ptAct.comp M.subtype

theorem himg_closure {G X : Type*} [Group G] [DecidableEq X] {ρ : G →* Equiv.Perm X} {m : ℕ}
    {F : Fin m → Finset X} (hF : Function.Injective F) {S : Set G}
    (hS : ∀ s ∈ S, ∀ i, ∃ j, (F i).image (ρ s) = F j) :
    ∀ h ∈ closure S, ∀ i, ∃ j, (F i).image (ρ h) = F j := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => intro i; exact ⟨i, by simp⟩
  | mul a b _ _ ha hb =>
    intro i
    obtain ⟨j, hj⟩ := hb i
    obtain ⟨k, hk⟩ := ha j
    exact ⟨k, by rw [map_mul, Equiv.Perm.coe_mul, ← Finset.image_image, hj, hk]⟩
  | inv a _ ha =>
    intro i
    choose f hf using ha
    have hinj : Function.Injective f := by
      intro i₁ i₂ h12
      apply hF
      have e1 := hf i₁
      have e2 := hf i₂
      rw [h12, ← e2] at e1
      exact Finset.image_injective (ρ a).injective e1
    obtain ⟨i', hi'⟩ := (Finite.injective_iff_surjective.1 hinj) i
    refine ⟨i', ?_⟩
    rw [← hi', ← hf i', Finset.image_image, map_inv]
    simp

@[expose] def k1G : GM := ⟨k1M, eM_mem _⟩

@[expose] def k2G : GM := ⟨k2M, eM_mem _⟩

@[expose] def K0G : Subgroup GM := Subgroup.closure {k1G, k2G, zG}

theorem chkK0_parts : (eM rK1 * xM 0 = xM 0 * eM rK1 ∧ eM rK2 * xM 0 = xM 0 * eM rK2) ∧
    eM rY1 = xM 1 ∧ eM rY3 = eM rX12 :=
  k0_facts

theorem K0G_le_centralizer : K0G ≤ centralizer {xG 0} := by
  rw [K0G, closure_le]
  intro g hg
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  rcases hg with rfl | rfl | rfl
  · exact Subtype.ext chkK0_parts.1.1
  · exact Subtype.ext chkK0_parts.1.2
  · exact zG_central _

theorem sK_vals : (∀ i : Fin 6, (sK1 i).val = sigK1.getD i.val 6) ∧
    ∀ i : Fin 6, (sK2 i).val = sigK2.getD i.val 6 := by
  decide

theorem image_blockF_of_maps
    {g : GM} {σ : Perm (Fin 6)} {l : List ℕ} (hσ : ∀ i : Fin 6, (σ i).val = l.getD i.val 6)
    (h : MapsB g.1 l) : ∀ i, (blockF i).image (rhoM g) = blockF (σ i) := by
  intro i
  apply image_eq_of_subset rhoM
  · intro U hU
    obtain ⟨d, hd, rfl⟩ := mem_blockF.1 hU
    obtain ⟨u, hu, hb, he⟩ := h (10 * i.val + d) (by omega)
    have hl : i.val < l.length := by
      by_contra hne
      have := hσ i
      rw [List.getD_eq_default _ _ (by omega)] at this
      have := (σ i).isLt
      omega
    have e1 : (10 * i.val + d) / 10 = i.val := by omega
    rw [e1, List.getD_eq_getElem _ _ hl] at hb
    have hσi := hσ i
    rw [List.getD_eq_getElem _ _ hl] at hσi
    change ptAct g.1 (pt (10 * i.val + d)) ∈ _
    rw [he, pt_mem_blockF hu, hb, hσi]
  · rw [card_blockF, card_blockF]

theorem blocks_maps :
    (MapsB (eM rK1) sigK1 ∧ MapsB (eM rK2) sigK2 ∧ MapsB (eM 7) [0, 1, 2, 3, 4, 5]) ∧
      ∀ t < 60, ptAct (eM (rX.getD 0 0)) (pt 0) ≠ pt t :=
  blocks_facts

theorem zG_val : zG.1 = eM 7 := zM_eq.symm

theorem himg_gens : ∀ s ∈ ({k1G, k2G, zG} : Set GM), ∀ i, ∃ j,
    (blockF i).image (rhoM s) = blockF j := by
  obtain ⟨⟨h1, h2, h3⟩, -⟩ := blocks_maps
  rintro s (rfl | rfl | rfl) i
  · exact ⟨_, image_blockF_of_maps sK_vals.1 h1 i⟩
  · exact ⟨_, image_blockF_of_maps sK_vals.2 h2 i⟩
  · exact ⟨_, image_blockF_of_maps (g := zG) (σ := 1) (l := [0, 1, 2, 3, 4, 5]) (by decide)
      (by rw [zG_val]; exact h3) i⟩

theorem himg_K0 : ∀ h ∈ K0G, ∀ i, ∃ j, (blockF i).image (rhoM h) = blockF j :=
  himg_closure blockF_injective himg_gens

@[expose] def actK : K0G →* Perm (Fin 6) := setAct blockF_injective himg_K0

theorem k1_mem : k1G ∈ K0G := subset_closure (by simp)

theorem k2_mem : k2G ∈ K0G := subset_closure (by simp)

theorem zG_mem_K0 : zG ∈ K0G := subset_closure (by simp)

theorem actK_k1 : actK ⟨k1G, k1_mem⟩ = sK1 :=
  setAct_eq_of_image blockF_injective himg_K0
    (image_blockF_of_maps sK_vals.1 blocks_maps.1.1)

theorem actK_k2 : actK ⟨k2G, k2_mem⟩ = sK2 :=
  setAct_eq_of_image blockF_injective himg_K0
    (image_blockF_of_maps sK_vals.2 blocks_maps.1.2.1)

theorem actK_z : actK ⟨zG, zG_mem_K0⟩ = 1 :=
  setAct_eq_of_image blockF_injective himg_K0
    (image_blockF_of_maps (g := zG) (σ := 1) (l := [0, 1, 2, 3, 4, 5]) (by decide)
      (by rw [zG_val]; exact blocks_maps.1.2.2))

theorem range_actK : actK.range = alternatingGroup (Fin 6) := by
  have htop : Subgroup.closure (((↑) : K0G → GM) ⁻¹' ({k1G, k2G, zG} : Set GM)) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [← closure_sK_eq_alt, MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure]
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨⟨g, hg⟩, hgS, rfl⟩
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hgS
    rcases hgS with rfl | rfl | rfl
    · rw [actK_k1]; exact subset_closure (by simp)
    · rw [actK_k2]; exact subset_closure (by simp)
    · rw [actK_z]; exact one_mem _
  · rw [closure_le]
    intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hσ
    rcases hσ with rfl | rfl
    · exact subset_closure ⟨⟨k1G, k1_mem⟩, by simp, actK_k1⟩
    · exact subset_closure ⟨⟨k2G, k2_mem⟩, by simp, actK_k2⟩

theorem zK0_mem_ker : (⟨zG, zG_mem_K0⟩ : K0G) ∈ actK.ker := actK_z

theorem card_zpowers_zK0 : Nat.card (zpowers (⟨zG, zG_mem_K0⟩ : K0G)) = 3 := by
  rw [Nat.card_zpowers]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (Subtype.ext relG.xcube) (fun h => relG.x1 (congrArg Subtype.val h))

theorem card_K0G_ge : 1080 ≤ Nat.card K0G := by
  have h := Subgroup.card_ker_mul_card_range actK
  rw [range_actK, card_alt_six] at h
  have hk : 3 ≤ Nat.card actK.ker := by
    rw [← card_zpowers_zK0]
    exact Subgroup.card_le_of_le ((zpowers_le).2 zK0_mem_ker)
  omega

theorem x0_off_blocks {j : Fin 6}
    (hj : (blockF 0).image (rhoM (xG 0)) = blockF j) : False := by
  have hpt : pt 0 ∈ blockF 0 := (pt_mem_blockF (by norm_num)).2 rfl
  have himg := Finset.mem_image_of_mem (rhoM (xG 0)) hpt
  rw [hj, mem_blockF] at himg
  obtain ⟨d, hd, e⟩ := himg
  exact blocks_maps.2 (10 * j.val + d) (by omega) e.symm

theorem xG0_not_mem_K0 : xG 0 ∉ K0G := by
  intro hx
  obtain ⟨j, hj⟩ := himg_K0 _ hx 0
  exact x0_off_blocks hj

theorem orderOf_xG0 : orderOf (xG 0) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (relG.vcube 0) (fun h => xG0_not_mem_K0 (h ▸ one_mem _))

theorem zpowers_inf_K0 : zpowers (xG 0) ⊓ K0G = ⊥ := by
  rw [eq_bot_iff]
  intro g ⟨hg1, hg2⟩
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg1
  rw [mem_bot]
  by_contra hne
  apply xG0_not_mem_K0
  have hn : ¬ (3 : ℤ) ∣ n := fun h3 => hne (by
    obtain ⟨m, rfl⟩ := h3
    rw [zpow_mul, show xG 0 ^ (3 : ℤ) = 1 from by rw [zpow_ofNat]; exact relG.vcube 0, one_zpow])
  have hcop : IsCoprime n 3 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Int.gcd_dvd_right (a := n) (b := 3)
    have h3p : Prime (3 : ℤ) := Int.prime_three
    rcases (Nat.dvd_prime Nat.prime_three).1 (Int.natCast_dvd_natCast.1 (by
      simpa using this)) with h | h
    · exact h
    · exfalso
      apply hn
      have := Int.gcd_dvd_left (a := n) (b := 3)
      rw [h] at this
      exact_mod_cast this
  obtain ⟨u, v, huv⟩ := hcop
  have : xG 0 = (xG 0 ^ n) ^ u := by
    rw [← zpow_mul, show n * u = 1 - 3 * v by linarith, zpow_sub, zpow_one, zpow_mul,
      show xG 0 ^ (3 : ℤ) = 1 from by rw [zpow_ofNat]; exact relG.vcube 0, one_zpow, inv_one,
      mul_one]
  rw [this]
  exact K0G.zpow_mem hg2 u

theorem centralizer_x0_eq : centralizer {xG 0} = zpowers (xG 0) ⊔ K0G ∧ Nat.card K0G = 1080 := by
  have hle : zpowers (xG 0) ⊔ K0G ≤ centralizer {xG 0} := by
    refine sup_le ?_ K0G_le_centralizer
    rw [zpowers_le, mem_centralizer_singleton_iff]
  let f : zpowers (xG 0) × K0G → (zpowers (xG 0) ⊔ K0G : Subgroup GM) := fun p =>
    ⟨p.1 * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, k⟩ ⟨a', k'⟩ h
    have e : (a : GM) * k = a' * k' := congrArg Subtype.val h
    have hm : (a' : GM)⁻¹ * a = k' * (k : GM)⁻¹ := by
      calc (a' : GM)⁻¹ * a = (a' : GM)⁻¹ * (a * k) * (k : GM)⁻¹ := by group
        _ = k' * (k : GM)⁻¹ := by rw [e]; group
    have h1 : (a' : GM)⁻¹ * a ∈ zpowers (xG 0) ⊓ K0G :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem a'.2) a.2, hm ▸ mul_mem k'.2 (inv_mem k.2)⟩
    rw [zpowers_inf_K0, mem_bot] at h1
    have ha : (a : GM) = a' := by
      calc (a : GM) = a' * ((a' : GM)⁻¹ * a) := by group
        _ = a' := by rw [h1, mul_one]
    have hk : (k : GM) = k' := by
      rw [ha] at e
      exact mul_left_cancel e
    rw [Prod.mk.injEq]
    exact ⟨Subtype.ext ha, Subtype.ext hk⟩
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_zpowers, orderOf_xG0] at h1
  have h2 := Subgroup.card_le_of_le hle
  have h3 := card_centralizer_x0_le
  have h4 := card_K0G_ge
  have hcard : Nat.card K0G = 1080 := by omega
  refine ⟨?_, hcard⟩
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem card_ker_actK : Nat.card actK.ker = 3 := by
  have h := Subgroup.card_ker_mul_card_range actK
  rw [range_actK, card_alt_six, centralizer_x0_eq.2] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 360) (h.trans (by norm_num))

theorem ker_actK : actK.ker = zpowers (⟨zG, zG_mem_K0⟩ : K0G) := by
  symm
  apply Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 zK0_mem_ker)
  rw [card_ker_actK, card_zpowers_zK0]

theorem isExtOf_K0 : CFSG.RankThree.PartTwo.Sec4.IsExtOf K0G (alternatingGroup (Fin 6))
    (Multiplicative (ZMod 3)) :=
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.isExtOf_of_hom actK range_actK card_ker_actK

end CFSG.RankThree.Native.ONTriple
