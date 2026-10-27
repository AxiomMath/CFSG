module

public import CFSG.Quasithin.Background.Harris.R1.QbetaDAbelT
public import CFSG.Quasithin.Background.Harris.R1.QbetaDAbelCore
public import CFSG.Quasithin.Background.Harris.R1.QbetaFin
public import CFSG.Quasithin.Background.Harris.R1.QbetaGen
public import CFSG.Quasithin.Background.Harris.R1.QbetaInst
public import CFSG.Quasithin.Background.Harris.R1.QbetaK1
public import CFSG.Quasithin.Background.Harris.R1.QbetaKerS

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7
  CFSG.Quasithin.A5Model CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem K1_comm_kerMD (C : FamCtx K1 L2 S Zs (Fin 5))
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hZS : ∀ u ∈ S, (∀ s ∈ S, u * s = s * u) → u * u = 1 → u ∈ Zs)
    (hker : ∀ k : ↥K1, C.D.act k = 1 → (k : G) ∈ pCoreOf 2 K1)
    (hW32 : Nat.card ↥(vBeta K1 L2 S Zs) = 32) :
    ∀ k ∈ K1, ∀ d ∈ C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G),
      k * d = d * k := by
  classical
  have hc5 : Fintype.card (Fin 5) = 5 := Fintype.card_fin 5
  have hij : (0 : Fin 5) ≠ 1 := by decide
  obtain ⟨g, y, z, h, h4⟩ := qd_of_famCtx C hc5 hij (List.finRange 5) (List.nodup_finRange 5)
    List.mem_finRange hcen hZS
  have hkS : C.kerM ≤ S := kerM_le_S C hker
  have hMeq : C.kerM ⊓ S = C.kerM := inf_eq_left.mpr hkS
  have hVA' : Zs ⊔ conjSub g Zs ≤ conjSub g (vBeta K1 L2 S Zs) ⊓ pCoreOf 2 (L2 ⊔ S) := by
    refine le_inf ?_ h.V_le_Q
    calc Zs ⊔ conjSub g Zs = conjSub g (Zs ⊔ conjSub g Zs) :=
          (F7.conjSub_eq_of_mem_normalizer (h.hVN h.hg)).symm
      _ ≤ conjSub g (vBeta K1 L2 S Zs) := conjSub_mono g h.V_le_W
  obtain ⟨a1, ha1, a2, ha2, hgen⟩ := exists_two_gen hVA' h4 (h.card_A' hW32)
  have hK1 : ⁅K1, K1⁆ = K1 := perfect_of_mem_cComp C.h.cComp_mem
  have hK1D : K1 ≤ Subgroup.normalizer
      ((C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G) : Subgroup G) : Set G) := by
    rw [hMeq]
    refine F7.le_normalizer_inf (le_sup_left.trans C.sup_le_normalizer_kerM) (fun k hk => ?_)
    have hWc : conjSub k (vBeta K1 L2 S Zs) = vBeta K1 L2 S Zs :=
      F7.conjSub_eq_of_mem_normalizer
        (le_normalizer_conjClosure (conjClosure Zs L2) (K1 ⊔ S) (Subgroup.mem_sup_left hk))
    apply Vert.mem_normalizer_of_conjSub_eq
    rw [← conjSub_centralizer, hWc]
  have hK1Z : ∀ k ∈ K1, ∀ s ∈ Zs, k * s = s * k := fun k hk s hs =>
    (Subgroup.mem_centralizer_iff.mp (C.h.K1_cent_Z hk) s hs).symm
  exact fun k hk d hd => h.K1_comm_D hK1 hK1D hK1Z ha1 ha2 hgen C.h.card_Z hk hd

theorem kerMD_abelian (C : FamCtx K1 L2 S Zs (Fin 5)) (hpt : C.D.pt = 4)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hZS : ∀ u ∈ S, (∀ s ∈ S, u * s = s * u) → u * u = 1 → u ∈ Zs)
    (hker : ∀ k : ↥K1, C.D.act k = 1 → (k : G) ∈ pCoreOf 2 K1)
    (hW32 : Nat.card ↥(vBeta K1 L2 S Zs) = 32) (h3 : ∃ k : ↥K1, C.D.act k = c3) :
    ∀ a ∈ C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G),
    ∀ b ∈ C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G), a * b = b * a := by
  classical
  have hc5 : Fintype.card (Fin 5) = 5 := Fintype.card_fin 5
  have hij : (0 : Fin 5) ≠ 1 := by decide
  have hKcomm := K1_comm_kerMD C hcen hZS hker hW32
  obtain ⟨g, y, z, h, h4⟩ := qd_of_famCtx C hc5 hij (List.finRange 5) (List.nodup_finRange 5)
    List.mem_finRange hcen hZS
  set D := C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G) with hD
  have hkS : C.kerM ≤ S := kerM_le_S C hker
  have hDS : D ≤ S := inf_le_left.trans inf_le_right
  have hyp := C.amalgamHypV
  have hVle : Zs ⊔ conjSub g Zs ≤ conjClosure Zs L2 := by
    refine sup_le (le_conjClosure Zs L2) ?_
    calc conjSub g Zs ≤ conjSub g (conjClosure Zs L2) := conjSub_mono g (le_conjClosure Zs L2)
      _ = conjClosure Zs L2 := F7.conjSub_eq_of_mem_normalizer (hyp.normalizes h.hg)
  have hVeq : Zs ⊔ conjSub g Zs = conjClosure Zs L2 :=
    Subgroup.eq_of_le_of_card_ge hVle (by rw [h4, C.h.V_card])
  obtain ⟨t, ht3, htact⟩ := exists_t3 C hker h3
  have htB : (t : G) ∈ borelOf K1 S := (C.D.stab t).mp (by
    show C.D.act t C.D.pt = C.D.pt
    rw [hpt, htact]
    exact c3_four)
  have htL2 : (t : G) ∈ Subgroup.normalizer (L2 : Set G) := C.h.hyp.h2.borel_le htB
  have htV : (t : G) ∈ Subgroup.normalizer ((Zs ⊔ conjSub g Zs : Subgroup G) : Set G) := by
    rw [hVeq]
    exact C.hVn htB
  have hT3 : (t : G) ^ 3 = 1 := by
    have := congrArg Subtype.val ht3
    simpa using this
  have hTZ : ∀ s ∈ Zs, (t : G) * s = s * (t : G) := fun s hs =>
    (Subgroup.mem_centralizer_iff.mp (C.h.K1_cent_Z t.2) s hs).symm
  have htVc : ∀ v ∈ conjClosure Zs L2, (t : G) * v * (t : G)⁻¹ = v := by
    rw [← hVeq]
    exact h.cent_V_of_three htV hTZ hT3
  obtain ⟨T, hTdef⟩ : ∃ T : G, T = (t : G) := ⟨_, rfl⟩
  rw [← hTdef] at hT3 htVc hTZ htL2
  have hT3' : T * T * T = 1 := by
    calc T * T * T = T ^ 3 := (pow_three' T).symm
      _ = 1 := hT3
  have hTK : T ∈ K1 := by rw [hTdef]; exact t.2
  obtain ⟨l, hl, s, hs, hgls⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes C.h.hyp.h2.normalizes).mp h.hg
  obtain ⟨x, hx⟩ : ∃ x : G, x = l⁻¹ := ⟨_, rfl⟩
  have hlx : l = x⁻¹ := by rw [hx]; simp
  have hxL : x ∈ L2 := by rw [hx]; exact L2.inv_mem hl
  have hxP : x ∈ L2 ⊔ S := Subgroup.mem_sup_left hxL
  have hxP' : x⁻¹ ∈ L2 ⊔ S := (L2 ⊔ S).inv_mem hxP
  have hQN : L2 ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 (L2 ⊔ S) : Set G) :=
    le_normalizer_pCoreOf 2 (L2 ⊔ S)
  have hSM : S ≤ Subgroup.normalizer ((C.kerM ⊓ S : Subgroup G) : Set G) :=
    F7.le_normalizer_inf (le_sup_right.trans C.sup_le_normalizer_kerM) Subgroup.le_normalizer
  have hDM : D ⊓ conjSub x⁻¹ (C.kerM ⊓ S) ≤ Zs := by
    have := h.D_inf_conjSub_M_le_Z
    rw [hgls, conjSub_mul, F7.conjSub_eq_of_mem_normalizer (hSM hs), hlx] at this
    exact this
  have hcL : T * x * T⁻¹ * x⁻¹ ∈ L2 :=
    L2.mul_mem ((Subgroup.mem_normalizer_iff.mp htL2 x).mp hxL) (L2.inv_mem hxL)
  have hcV : ∀ v ∈ conjClosure Zs L2,
      v * (T * x * T⁻¹ * x⁻¹) = (T * x * T⁻¹ * x⁻¹) * v := by
    intro v hv
    have hv1 : x⁻¹ * v * x ∈ conjClosure Zs L2 := by
      have := (Subgroup.mem_normalizer_iff.mp (hyp.normalizes hxP') v).mp hv
      simpa using this
    have e1 : T * (x⁻¹ * v * x) * T⁻¹ = x⁻¹ * v * x := htVc _ hv1
    have e2 : T * v * T⁻¹ = v := htVc v hv
    have e1' : T⁻¹ * (x⁻¹ * v * x) * T = x⁻¹ * v * x := by
      calc T⁻¹ * (x⁻¹ * v * x) * T = T⁻¹ * (T * (x⁻¹ * v * x) * T⁻¹) * T := by rw [e1]
        _ = x⁻¹ * v * x := by group
    have hcv : (T * x * T⁻¹ * x⁻¹) * v * (T * x * T⁻¹ * x⁻¹)⁻¹ = v := by
      calc (T * x * T⁻¹ * x⁻¹) * v * (T * x * T⁻¹ * x⁻¹)⁻¹
          = T * x * (T⁻¹ * (x⁻¹ * v * x) * T) * x⁻¹ * T⁻¹ := by group
        _ = T * x * (x⁻¹ * v * x) * x⁻¹ * T⁻¹ := by rw [e1']
        _ = T * v * T⁻¹ := by group
        _ = v := e2
    exact (mul_inv_eq_iff_eq_mul.mp hcv).symm
  have hcQ : T * x * T⁻¹ * x⁻¹ ∈ pCoreOf 2 (L2 ⊔ S) :=
    cent_le_pCore C (Subgroup.mem_sup_left hcL) hcV
  obtain ⟨q, hq⟩ : ∃ q : G, q = x⁻¹ * T * x * T⁻¹ := ⟨_, rfl⟩
  have hqQ : q ∈ pCoreOf 2 (L2 ⊔ S) := by
    have := (Subgroup.mem_normalizer_iff.mp (hQN hxP') (T * x * T⁻¹ * x⁻¹)).mp hcQ
    have e : x⁻¹ * (T * x * T⁻¹ * x⁻¹) * x⁻¹⁻¹ = q := by rw [hq]; group
    rwa [e] at this
  have hqS : q ∈ S := C.pCore_le_S hqQ
  have hqN : q ∈ Subgroup.normalizer (D : Set G) := h.hDS hqS
  have hqcop : Nat.Coprime 3 (orderOf q) := by
    obtain ⟨k, hk⟩ := h.hS2 ⟨q, hqS⟩
    have hk' : q ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk')
      (Nat.Coprime.pow_right k (by norm_num))
  have hact : ∀ d ∈ D, (x⁻¹ * T * x) * d * (x⁻¹ * T * x)⁻¹ = q * d * q⁻¹ := by
    intro d hd
    have hTd : T * d = d * T := hKcomm T hTK d hd
    calc (x⁻¹ * T * x) * d * (x⁻¹ * T * x)⁻¹
        = (x⁻¹ * T * x * T⁻¹) * (T * d * T⁻¹) * (x⁻¹ * T * x * T⁻¹)⁻¹ := by group
      _ = q * d * q⁻¹ := by rw [hTd, hq]; group
  have ht'3 : (x⁻¹ * T * x) ^ 3 = 1 := by
    calc (x⁻¹ * T * x) ^ 3 = (x⁻¹ * T * x) * (x⁻¹ * T * x) * (x⁻¹ * T * x) := pow_three' _
      _ = x⁻¹ * (T * T * T) * x := by group
      _ = 1 := by rw [hT3']; group
  have hcent : ∀ d ∈ D, (x⁻¹ * T * x) * d * (x⁻¹ * T * x)⁻¹ = d :=
    conj_eq_of_two_pow D q (x⁻¹ * T * x) hqcop hqN ht'3 hact
  have hTE : ∀ e : G, x⁻¹ * e * x ∈ D → T * e = e * T := by
    intro e he
    have h1 := hcent _ he
    have h2 : T * e * T⁻¹ = e := by
      calc T * e * T⁻¹ = x * ((x⁻¹ * T * x) * (x⁻¹ * e * x) * (x⁻¹ * T * x)⁻¹) * x⁻¹ := by group
        _ = x * (x⁻¹ * e * x) * x⁻¹ := by rw [h1]
        _ = e := by group
    exact (mul_inv_eq_iff_eq_mul.mp h2)
  have hEQ : conjSub x D ≤ pCoreOf 2 (L2 ⊔ S) := by
    intro e he
    have hd : x⁻¹ * e * x ∈ D := mem_conjSub.mp he
    have hdQ : x⁻¹ * e * x ∈ pCoreOf 2 (L2 ⊔ S) := h.D_le_Q hd
    have := (Subgroup.mem_normalizer_iff.mp (hQN hxP) (x⁻¹ * e * x)).mp hdQ
    have e' : x * (x⁻¹ * e * x) * x⁻¹ = e := by group
    rwa [e'] at this
  have hES : conjSub x D ≤ S := fun e he => C.pCore_le_S (hEQ he)
  have hEH : conjSub x D ≤ K1 ⊔ S := hES.trans le_sup_right
  let f : ↥(conjSub x D) →* Equiv.Perm (Fin 5) :=
    (permHom C).comp (Subgroup.inclusion hEH)
  have hc3 : permHom C ⟨T, by rw [hTdef]; exact Subgroup.mem_sup_left t.2⟩ = c3 := by
    have := permHom_K1 C t
    rw [← htact, ← this]
    congr 1
    exact Subtype.ext hTdef
  have hrange2 : IsPGroup 2 ↥f.range :=
    (h.hS2.to_le hES : IsPGroup 2 ↥(conjSub x D)).of_surjective f.rangeRestrict
      f.rangeRestrict_surjective
  have hrcomm : ∀ p ∈ f.range, p * c3 = c3 * p := by
    intro p hp
    obtain ⟨e, rfl⟩ := hp
    have hT := hTE (e : G) (mem_conjSub.mp e.2)
    rw [← hc3]
    show permHom C (Subgroup.inclusion hEH e) *
        permHom C ⟨T, by rw [hTdef]; exact Subgroup.mem_sup_left t.2⟩ =
      permHom C ⟨T, by rw [hTdef]; exact Subgroup.mem_sup_left t.2⟩ *
        permHom C (Subgroup.inclusion hEH e)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hT.symm
  have hrange : Nat.card ↥f.range ≤ 2 := card_le_two_of_pGroup f.range hrange2 hrcomm
  have hZmem : ∀ e : ↥f.ker, x⁻¹ * (((e : ↥(conjSub x D)) : G)) * x ∈ Zs := by
    intro e
    have hf : f e = 1 := e.2
    have hM : (((e : ↥(conjSub x D)) : G)) ∈ C.kerM :=
      (permHom_eq_one_iff C (Subgroup.inclusion hEH e)).1 hf
    have hd : x⁻¹ * (((e : ↥(conjSub x D)) : G)) * x ∈ D := mem_conjSub.mp (e : ↥(conjSub x D)).2
    refine hDM (Subgroup.mem_inf.mpr ⟨hd, ?_⟩)
    rw [mem_conjSub]
    have e' : x⁻¹⁻¹ * (x⁻¹ * (((e : ↥(conjSub x D)) : G)) * x) * x⁻¹ =
        (((e : ↥(conjSub x D)) : G)) := by group
    rw [e']
    exact ⟨hM, hES (e : ↥(conjSub x D)).2⟩
  have hkerle : Nat.card ↥f.ker ≤ 2 := by
    rw [← C.h.card_Z]
    refine Nat.card_le_card_of_injective
      (fun e : ↥f.ker => (⟨x⁻¹ * (((e : ↥(conjSub x D)) : G)) * x, hZmem e⟩ : ↥Zs)) ?_
    intro e1 e2 hne
    have h1 : x⁻¹ * (((e1 : ↥(conjSub x D)) : G)) * x = x⁻¹ * (((e2 : ↥(conjSub x D)) : G)) * x :=
      congrArg Subtype.val hne
    have h2 : (((e1 : ↥(conjSub x D)) : G)) = (((e2 : ↥(conjSub x D)) : G)) :=
      mul_left_cancel (mul_right_cancel h1)
    exact Subtype.ext (Subtype.ext h2)
  have hcardE : Nat.card ↥(conjSub x D) = Nat.card ↥f.range * Nat.card ↥f.ker := by
    have h1 := Subgroup.index_mul_card f.ker
    rw [Subgroup.index_ker] at h1
    exact h1.symm
  have hcardD : Nat.card ↥D ≤ 4 := by
    have h1 : Nat.card ↥(conjSub x D) = Nat.card ↥D := CosetGeom.card_conjSub x D
    rw [← h1, hcardE]
    exact (Nat.mul_le_mul hrange hkerle).trans (by norm_num)
  exact abelian_of_card_le_four D (h.hS2.to_le hDS) hcardD

end CFSG.Quasithin.Background.Harris.R1
