module

public import CFSG.Quasithin.H13.L32AC47m
public import CFSG.Quasithin.H13.L32AC47n
public import CFSG.Quasithin.H13.L32AC36c
public import CFSG.Quasithin.Background.B5Part3
public import CFSG.Quasithin.H13.L32A770k
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.QuasithinUnique.Vol2Native.A312L.Seven

attribute [local instance] commGroupOfFact

theorem card_sl32 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_modEq_one_of_cube {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {y : MulAut W} (hy3 : y ^ 3 = 1) (hcube : ∀ w, w * y w * y (y w) = 1) {S : Subgroup W}
    (hS : ∀ s ∈ S, y s ∈ S) : Nat.card S ≡ 1 [MOD 3] := by
  classical
  have : Fintype S := Fintype.ofFinite _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : Function.End ↥S := fun s => ⟨y s, hS s s.2⟩
  have hyyy : ∀ w, y (y (y w)) = w := fun w => by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_three', hy3, MulAut.one_apply]
  have hf : f ^ 3 ^ 1 = 1 := by
    funext s
    apply Subtype.ext
    show y (y (y s)) = s
    exact hyyy s
  have hfix : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, Subtype.ext (map_one y)⟩, fun z => ?_⟩
    have hz : y z = z := congrArg Subtype.val z.2
    have h1 := hcube z
    rw [hz, hz, hW, one_mul] at h1
    exact Subtype.ext (Subtype.ext h1)
  have h := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
  rw [Nat.card_eq_fintype_card]
  rw [hfix] at h
  exact h

theorem relIndex_eq_eight_of_d310Two {W : Type} [CommGroup W] [Finite W]
    {T L : Subgroup (MulAut W)} {U : Subgroup W} (h : D310Two T L U) (hc : Nat.card L = 168) :
    (U ⊓ fixV L).relIndex U = 8 := by
  have hv : padicValNat 2 (Nat.card L) = 3 := by
    rw [hc]
    exact padicValNat_two_pow_mul_odd (a := 3) (u := 21) (by decide)
  obtain ⟨hcases, -, -⟩ := h
  rcases hcases with ⟨n, K, _, _, hK, π, hπ⟩ | ⟨n, K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ |
    ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨α, π, hπ⟩
  ·
    have hn := one_le_of_card_field hK
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hX0 : Nat.card L = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    have hX : Nat.card L = 2 ^ (n * 3) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1)) := by
      rw [hX0, card_statedSL_three1527d, hK, ← pow_mul, ← pow_mul]
    rw [hX, padicValNat_two_pow_mul_odd ((odd_two_pow_sub_one_of_pos (by omega)).mul
      (odd_two_pow_sub_one_of_pos (by omega)))] at hv
    have hn1 : n = 1 := by omega
    subst hn1
    obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, -⟩ := hπ
    have hker : β.ker = (U ⊓ fixV L).subgroupOf U := by
      ext u
      rw [MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ hβs,
      Subgroup.card_top, ← Subgroup.index_eq_card]
    show ((⊥ : Subgroup (Multiplicative (Fin 3 → K))).subgroupOf ⊤).index = 8
    rw [Subgroup.bot_subgroupOf, Subgroup.index_bot, Subgroup.card_top]
    show Nat.card (Fin 3 → K) = 8
    rw [Nat.card_fun, Nat.card_fin, hK]
    norm_num
  ·
    have hn := one_le_of_card_field hK
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    have hX0 : Nat.card L = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    have hX : Nat.card L = 2 ^ (n * 4) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 4) - 1)) := by
      rw [hX0, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK, hI,
        Finset.prod_pair (by norm_num), ← pow_mul, ← pow_mul, ← pow_mul]
      norm_num
    rw [hX, padicValNat_two_pow_mul_odd ((odd_two_pow_sub_one_of_pos (by omega)).mul
      (odd_two_pow_sub_one_of_pos (by omega)))] at hv
    omega
  ·
    have h1 : Nat.card L ∣ Nat.card ↥(alternatingGroup (Fin 6)) :=
      Subgroup.card_dvd_of_surjective hπ.1
    rw [card_alternatingGroup1527d 6 (by norm_num), hc] at h1
    norm_num [Nat.factorial] at h1
  ·
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hX : Nat.card L = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    rw [hX, card_statedSL1527d (d := 4) (by norm_num), hK] at hc
    norm_num [Finset.prod_Icc_succ_top] at hc
  ·
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hX : Nat.card L = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    rw [hX, card_statedSL1527d (d := 5) (by norm_num), hK] at hc
    norm_num [Finset.prod_Icc_succ_top] at hc
  ·
    have hS : IsSimpleGroup (FFModel.a7Four α).Gam :=
      alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
    have h7 : Nat.card (FFModel.a7Four α).Gam = 2520 := by
      show Nat.card ↥(alternatingGroup (Fin 7)) = 2520
      rw [card_alternatingGroup1527d 7 (by norm_num)]
      norm_num [Nat.factorial]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hk | hk
    · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hk
      have := Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv
      omega
    · have h1 := Subgroup.card_ker_mul_card_of_surjective hπ.1
      rw [hk, Subgroup.card_top, h7, hc] at h1
      omega

theorem map_eq_of_mem_stabSub {W : Type*} [CommGroup W] {U : Subgroup W} {g : MulAut W}
    (h : g ∈ stabSub U) : U.map g.toMonoidHom = U := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (h v).mpr hv
  · intro hu
    refine ⟨g⁻¹ u, ?_, by simp⟩
    have h1 := h (g⁻¹ u)
    rw [MulAut.apply_inv_self] at h1
    exact h1.mp hu

theorem false_of_d310Two_of_cube {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {Mp T L : Subgroup (MulAut W)} {V : Subgroup W} (hMp : Mp = L)
    (hirr : XMod.IsIrrSec ↥Mp (XMod.fixed ↥Mp V) V) (hLs : L ≤ stabSub V)
    (hTL : ∀ s ∈ T, ∀ γ ∈ L, s * γ * s⁻¹ ∈ L) (hTL' : ∀ s ∈ T, ∀ γ ∈ L, s⁻¹ * γ * s ∈ L)
    (h3 : D310Two T L V) (h8 : (V ⊓ fixV L).relIndex V = 8)
    {y : MulAut W} (hy3 : y ^ 3 = 1) (hcube : ∀ w, w * y w * y (y w) = 1)
    (hyL : ∀ γ ∈ L, γ * y = y * γ) : False := by
  classical
  obtain ⟨-, ⟨s, hsT, hsV⟩, hall⟩ := h3
  obtain ⟨⟨hsum1, hsum2⟩, hniso⟩ := hall s hsT hsV
  have hyC : ∀ c ∈ fixV L, y c ∈ fixV L := fun c hc γ hγ => by
    rw [← MulAut.mul_apply, hyL γ hγ, MulAut.mul_apply, hc γ hγ]
  have hLA : ∀ γ ∈ L, ∀ a ∈ V ⊔ fixV L, γ a ∈ V ⊔ fixV L := by
    intro γ hγ a ha
    obtain ⟨v, hv, c, hc, rfl⟩ := Subgroup.mem_sup.mp ha
    rw [map_mul, hc γ hγ]
    exact (V ⊔ fixV L).mul_mem (Subgroup.mem_sup_left ((hLs hγ v).mpr hv))
      (Subgroup.mem_sup_right hc)
  have hyγ : ∀ γ ∈ L, ∀ w, y (γ w) = γ (y w) := fun γ hγ w => by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, hyL γ hγ]
  let J : Subgroup W :=
    { carrier := {u | u ∈ V ∧ y u ∈ V ⊔ fixV L}
      one_mem' := ⟨V.one_mem, by rw [map_one]; exact (V ⊔ fixV L).one_mem⟩
      mul_mem' := fun ha hb => ⟨V.mul_mem ha.1 hb.1, by
        rw [map_mul]; exact (V ⊔ fixV L).mul_mem ha.2 hb.2⟩
      inv_mem' := fun ha => ⟨V.inv_mem ha.1, by
        rw [map_inv]; exact (V ⊔ fixV L).inv_mem ha.2⟩ }
  have hfixC : ∀ u, u ∈ XMod.fixed ↥Mp V ↔ u ∈ V ⊓ fixV L := fun u => by
    constructor
    · rintro ⟨hu, hf⟩
      exact ⟨hu, fun γ hγ => hf ⟨γ, hMp ▸ hγ⟩⟩
    · rintro ⟨hu, hc⟩
      exact ⟨hu, fun a => hc a (hMp ▸ a.2)⟩
  have hJinv : XMod.IsInv ↥Mp J := by
    intro a u hu
    have ha : (a : MulAut W) ∈ L := hMp ▸ a.2
    refine ⟨(hLs ha u).mpr hu.1, ?_⟩
    show y ((a : MulAut W) u) ∈ V ⊔ fixV L
    rw [hyγ _ ha]
    exact hLA _ ha _ hu.2
  have hfJ : XMod.fixed ↥Mp V ≤ J := fun u hu => by
    obtain ⟨hu1, hu2⟩ := (hfixC u).mp hu
    exact ⟨hu1, Subgroup.mem_sup_right (hyC u hu2)⟩
  rcases hirr.2 J hJinv hfJ (fun u hu => hu.1) with hJ | hJ
  ·
    apply hniso
    rw [B5.secIsoL_iff]
    have hsC : s ∈ stabSub (fixV L) := mem_stabSub_fixV_of_conj (hTL s hsT) (hTL' s hsT)
    have hLB : ∀ γ ∈ L, ∀ m ∈ V.map s.toMonoidHom, γ m ∈ V.map s.toMonoidHom := by
      rintro γ hγ _ ⟨v, hv, rfl⟩
      refine ⟨(s⁻¹ * γ * s) v, (hLs (hTL' s hsT γ hγ) v).mpr hv, ?_⟩
      show s ((s⁻¹ * γ * s) v) = γ (s v)
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    refine ⟨inf_le_left, inf_le_left, fun h u hu => (hLs h.2 u).mpr hu,
      fun h z hz => ⟨(hLs h.2 z).mpr hz.1, by rw [hz.2 h h.2]; exact hz.2⟩,
      fun γ m hm => hLB _ γ.2 m hm,
      fun γ m hm => ⟨hLB _ γ.2 m hm.1, by rw [hm.2 γ γ.2]; exact hm.2⟩, ?_⟩
    let qB : ↥(V.map s.toMonoidHom) →* W ⧸ (V ⊔ fixV L) :=
      (QuotientGroup.mk' (V ⊔ fixV L)).comp (V.map s.toMonoidHom).subtype
    have hqB : Function.Surjective qB := by
      intro z
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (V ⊔ fixV L) z
      have hw : w ∈ V ⊔ V.map s.toMonoidHom ⊔ fixV L := hsum1 ▸ Subgroup.mem_top w
      obtain ⟨y₁, hy₁, c, hc, rfl⟩ := Subgroup.mem_sup.mp hw
      obtain ⟨v, hv, b, hb, rfl⟩ := Subgroup.mem_sup.mp hy₁
      refine ⟨⟨b, hb⟩, ?_⟩
      show (QuotientGroup.mk' (V ⊔ fixV L)) b = (QuotientGroup.mk' (V ⊔ fixV L)) (v * b * c)
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        show v * b * c = b * (v * c) by rw [mul_comm v b, mul_assoc], inv_mul_cancel_left]
      exact (V ⊔ fixV L).mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hc)
    have hkerB : qB.ker = (V.map s.toMonoidHom ⊓ fixV L).subgroupOf (V.map s.toMonoidHom) := by
      ext b
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show (QuotientGroup.mk' (V ⊔ fixV L)) (b : W) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      constructor
      · intro hbA
        exact ⟨b.2, hsum2 ⟨hbA, Subgroup.mem_sup_left b.2⟩⟩
      · intro hbC
        exact Subgroup.mem_sup_right hbC.2
    let eB := (QuotientGroup.quotientMulEquivOfEq hkerB.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective qB hqB)
    have heB : ∀ m : ↥(V.map s.toMonoidHom), eB (QuotientGroup.mk m) =
        QuotientGroup.mk (m : W) := fun m => rfl
    let β : ↥V →* ↥(V.map s.toMonoidHom) ⧸
        (V.map s.toMonoidHom ⊓ fixV L).subgroupOf (V.map s.toMonoidHom) :=
      eB.symm.toMonoidHom.comp
        ((QuotientGroup.mk' (V ⊔ fixV L)).comp (y.toMonoidHom.comp V.subtype))
    have hβ : ∀ u : ↥V, eB (β u) = QuotientGroup.mk (y u) := fun u => by
      show eB (eB.symm _) = _
      rw [MulEquiv.apply_symm_apply]
      rfl
    have hβ1 : ∀ u : ↥V, β u = 1 ↔ (u : W) ∈ V ⊓ fixV L := by
      intro u
      rw [← (hfixC u).trans Iff.rfl, ← hJ]
      constructor
      · intro h1
        have h2 := hβ u
        rw [h1, map_one] at h2
        exact ⟨u.2, (QuotientGroup.eq_one_iff _).mp h2.symm⟩
      · intro h1
        apply eB.injective
        rw [hβ, map_one]
        exact (QuotientGroup.eq_one_iff _).mpr h1.2
    refine ⟨β, ?_, hβ1, ?_⟩
    ·
      have hker : β.ker = (V ⊓ fixV L).subgroupOf V := by
        ext u
        rw [MonoidHom.mem_ker, hβ1, Subgroup.mem_subgroupOf]
      have hr : Nat.card β.range = 8 := by
        rw [← Subgroup.index_ker, hker]
        exact h8
      have hcod : Nat.card (↥(V.map s.toMonoidHom) ⧸
          (V.map s.toMonoidHom ⊓ fixV L).subgroupOf (V.map s.toMonoidHom)) = 8 := by
        rw [← Subgroup.index_eq_card]
        show (V.map s.toMonoidHom ⊓ fixV L).relIndex (V.map s.toMonoidHom) = 8
        have hC' : fixV L = (fixV L).map s.toMonoidHom := (map_eq_of_mem_stabSub hsC).symm
        rw [hC', ← Subgroup.map_inf_eq _ _ s.toMonoidHom s.injective,
          Subgroup.relIndex_map_map_of_injective _ _ s.injective]
        exact h8
      rw [← MonoidHom.range_eq_top]
      exact Subgroup.eq_top_of_card_eq _ (hr.trans hcod.symm)
    ·
      intro γ u m hu hm hum
      apply eB.injective
      rw [hβ, heB]
      have h1 := hβ u
      rw [hum, heB] at h1
      have h2 := (QuotientGroup.eq.mp h1)
      show QuotientGroup.mk (y ((γ : MulAut W) u)) = QuotientGroup.mk ((γ : MulAut W) m)
      rw [QuotientGroup.eq, hyγ _ γ.2, ← map_inv, ← map_mul]
      exact hLA _ γ.2 _ (by simpa using (V ⊔ fixV L).inv_mem h2)
  ·
    have hyA : ∀ a ∈ V ⊔ fixV L, y a ∈ V ⊔ fixV L := by
      intro a ha
      obtain ⟨v, hv, c, hc, rfl⟩ := Subgroup.mem_sup.mp ha
      rw [map_mul]
      have hvJ : v ∈ J := hJ ▸ hv
      exact (V ⊔ fixV L).mul_mem hvJ.2 (Subgroup.mem_sup_right (hyC c hc))
    have hA1 := card_modEq_one_of_cube hW hy3 hcube hyA
    have hC1 := card_modEq_one_of_cube hW hy3 hcube hyC
    have hidx : (fixV L).relIndex (V ⊔ fixV L) = 8 := by
      rw [Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_right, inf_comm]
      exact h8
    have h1 := Subgroup.relIndex_mul_card (fixV L) (V ⊔ fixV L)
    rw [inf_eq_left.mpr le_sup_right, hidx] at h1
    unfold Nat.ModEq at hA1 hC1
    omega

variable {G : Type} [Group G] [Finite G] {T L V H K I : Subgroup G}

theorem exists_cube_of_comm (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hHeq : H = K ⊔ (l1 T L V ⊔ T))
    (hcomm : ∀ x ∈ l1 T L V, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H)
    (hIU : I ≤ conjClosure V H) [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))] :
    ∃ y : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure I H)), y ^ 3 = 1 ∧
      (∀ w, w * y w * y (y w) = 1) ∧ ∀ γ ∈ autIH (fsuV1 T V) I H K, γ * y = y * γ := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨x, hxL1, hx3, hfpf⟩ := exists_l1_fpf S.hyp hMod h1222 h1332 h1334
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hxl : x ∈ l1 T L V := hl1eq ▸ hxL1
  have hHL := H_le_N_l1_of_comm S h1332 hHeq hcomm
  have hθ := cube_mem h1222 h1332 h1334 S hF hHL hxl hx3 hfpf
  have hIHN := hF.conjClosure_le_normalizer_V₁ hIU
  have hIHU : conjClosure I H ≤ conjClosure V H := conjClosure_le_conjClosure_U hIU le_rfl
  have hIH := le_normalizer_conjClosure I H
  have hxH : x ∈ H := Setting147.l1H' S hxl
  set ψ := actH hF.H_le_normalizer_V₁ hIH with hψ
  refine ⟨ψ ⟨x, hxH⟩, ?_, ?_, ?_⟩
  · have h1 : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [← map_pow, h1, map_one]
  · intro w
    obtain ⟨a, haI, haw⟩ := exists_mk_of_mem_tilde w
    have hwa : w = modMk hIHN (a : G) haI := Subtype.ext haw.symm
    have h1 := (Subgroup.mem_normalizer_iff.mp (hIH hxH) _).mp haI
    have h2 := (Subgroup.mem_normalizer_iff.mp (hIH hxH) _).mp h1
    have hθa := hθ (a : G) (hIHU haI)
    rw [hwa, actH_modMk hF.H_le_normalizer_V₁ hIHN hIH ⟨x, hxH⟩ haI,
      actH_modMk hF.H_le_normalizer_V₁ hIHN hIH ⟨x, hxH⟩ h1]
    apply Subtype.ext
    show secMk _ _ ⟨(a : G), _⟩ * secMk _ _ ⟨x * a * x⁻¹, _⟩ *
      secMk _ _ ⟨x * (x * a * x⁻¹) * x⁻¹, _⟩ = 1
    rw [← map_mul, ← map_mul]
    exact (secMk_eq_one_iff (A := Subgroup.normalizer (fsuV1 T V : Set G))
      (B := fsuV1 T V) (x := ⟨_, hIHN ((conjClosure I H).mul_mem
        ((conjClosure I H).mul_mem haI h1) h2)⟩)).mpr hθa
  · intro γ hγ
    rw [autIH_eq_map hF hKH] at hγ
    obtain ⟨k, hk, rfl⟩ := hγ
    have hc := hcomm x hxl k (Subgroup.mem_subgroupOf.mp hk)
    have h0 := hF.actH_eq_one_of_mem_pCoreOf hIU
      (x := ⟨x * (k : G) * x⁻¹ * (k : G)⁻¹, H.mul_mem (H.mul_mem (H.mul_mem hxH k.2)
        (H.inv_mem hxH)) (H.inv_mem k.2)⟩) hc
    have e0 : (⟨x * (k : G) * x⁻¹ * (k : G)⁻¹, H.mul_mem (H.mul_mem (H.mul_mem hxH k.2)
        (H.inv_mem hxH)) (H.inv_mem k.2)⟩ : ↥H) = ⟨x, hxH⟩ * k * ⟨x, hxH⟩⁻¹ * k⁻¹ := rfl
    have h1 : ψ (⟨x, hxH⟩ * k * ⟨x, hxH⟩⁻¹ * k⁻¹) = 1 := by
      rw [← e0]
      exact h0
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have e : ψ k * ψ ⟨x, hxH⟩ =
        (ψ ⟨x, hxH⟩ * ψ k * (ψ ⟨x, hxH⟩)⁻¹ * (ψ k)⁻¹)⁻¹ * (ψ ⟨x, hxH⟩ * ψ k) := by group
    rw [e, h1, inv_one, one_mul]

theorem false_of_d310Two (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hK₀ : conjClosure K T = K) (hHeq : H = K ⊔ (l1 T L V ⊔ T)) (hP : IsPSL 3 2 1 (cStar K))
    (hcomm : ∀ x ∈ l1 T L V, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H)
    (hV₁I : fsuV1 T V ≤ I) (hIU : I ≤ conjClosure V H) (hirrT : IsIrrPlusTildeT hF hIU)
    [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))]
    (h3 : D310Two (autIH (fsuV1 T V) I H T) (autIH (fsuV1 T V) I H K)
      (subM (fsuV1 T V) (conjClosure I H) I)) : False := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hTH : T ≤ H := hF.T_le_H
  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := hirrT
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hKI' : K ≤ Subgroup.normalizer (I : Set G) := hK₀ ▸ hKI
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have hMp : autIH (fsuV1 T V) I H (conjClosure K T) = autIH (fsuV1 T V) I H K := by rw [hK₀]
  obtain ⟨φ⟩ := isPSL_three_two_iff.mp hP
  have hSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := slThree_isSimple
  have hS' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := ((cStarEquiv K).symm.trans φ).isSimpleGroup
  have hne : autIH (fsuV1 T V) I H K ≠ ⊥ := by
    rw [autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  obtain ⟨e3⟩ := nonempty_mulEquiv_quotient_autI hF hIU hS' hne
  have hcard : Nat.card ↥(autIH (fsuV1 T V) I H K) = 168 := by
    rw [← Nat.card_congr e3.toEquiv, Nat.card_congr ((cStarEquiv K).symm.trans φ).toEquiv,
      card_sl32]
  have h8 := relIndex_eq_eight_of_d310Two h3 hcard
  obtain ⟨y, hy3, hcube, hyL⟩ := exists_cube_of_comm h1222 h1332 h1334 S hF hHeq hcomm hIU
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := fun s hs =>
    Subgroup.mem_normalizer_fintype fun k' hk' => by
      have := mem_conjClosure hs hk'
      rwa [hK₀] at this
  have hTL : ∀ s ∈ autIH (fsuV1 T V) I H T, ∀ γ ∈ autIH (fsuV1 T V) I H K,
      s * γ * s⁻¹ ∈ autIH (fsuV1 T V) I H K := by
    intro s hs γ hγ
    rw [autIH_eq_map hF hTH] at hs
    rw [autIH_eq_map hF hKH] at hγ ⊢
    obtain ⟨t, ht, rfl⟩ := hs
    obtain ⟨k, hk, rfl⟩ := hγ
    refine ⟨t * k * t⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hTK (Subgroup.mem_subgroupOf.mp ht)) _).mp
      (Subgroup.mem_subgroupOf.mp hk)
  have hTL' : ∀ s ∈ autIH (fsuV1 T V) I H T, ∀ γ ∈ autIH (fsuV1 T V) I H K,
      s⁻¹ * γ * s ∈ autIH (fsuV1 T V) I H K := by
    intro s hs γ hγ
    have h1 := hTL s⁻¹ ((autIH (fsuV1 T V) I H T).inv_mem hs) γ hγ
    simpa using h1
  have hW : ∀ w : ↥(tildeOf (fsuV1 T V) (conjClosure I H)), w * w = 1 := by
    intro w
    apply Subtype.ext
    have := (Fact.out : IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H))).2 w w.2
    simpa [pow_two] using this
  exact false_of_d310Two_of_cube hW hMp hirr'.1.2.2.2
    (autIH_le_stabSub_of hF hIU hV₁I hKH hKI') hTL hTL' h3 h8 hy3 hcube hyL

end CFSG.Quasithin.H13.L32A.C
