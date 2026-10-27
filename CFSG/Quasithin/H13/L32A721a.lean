module

public import CFSG.Quasithin.H13.L32A720c

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
include E

theorem zpowers_eq_l1dot {x : G} (hxL : x ∈ l1 T L V) (hxH : x ∈ hz T V) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) :
    Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) (⟨x, hxH⟩ : ↥(hz T V))) =
      modO2Image (hz T V) (l1 T L V) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set y := QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) (⟨x, hxH⟩ : ↥(hz T V)) with hy
  have hmem : y ∈ modO2Image (hz T V) (l1 T L V) := mem_modO2Image_iff.mpr ⟨⟨x, hxH⟩, hxL, rfl⟩
  have h3 : y ^ 3 = 1 := by
    rw [hy, ← map_pow]
    have e : (⟨x, hxH⟩ : ↥(hz T V)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [e, map_one]
  have h1 : y ≠ 1 := by
    intro h1
    rw [hy, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hxQ : x ∈ pCoreOf 2 (hz T V) := C2Six.mem_pCore_two_iff.mp h1
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (hz T V)) ⟨x, hxQ⟩
    have hxn : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨hx3, hxn⟩
    rw [hcop.gcd_eq_one, pow_one] at this
    exact hx1 this
  refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hmem) ?_
  rw [Nat.card_zpowers, orderOf_eq_prime h3 h1, E.card_l1dot]

theorem exists_three : ∃ x ∈ l1 T L V, x ∈ hz T V ∧ x ^ 3 = 1 ∧ x ≠ 1 := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  obtain ⟨x, hxL1, hx3, hfpf⟩ := exists_l1_fpf E.S.hyp hMod E.h1222 E.h1332 E.h1334
  obtain ⟨-, hV8, -, hV1, -⟩ := hMod G T L V E.S.hyp.hyp E.S.hyp.fsu
  have hx1 : x ≠ 1 := by
    intro h1
    obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ∉ fsuV1 T V := by
      by_contra hno
      push Not at hno
      have := Subgroup.card_le_of_le (show V ≤ fsuV1 T V from hno)
      rw [hV8, hV1] at this
      omega
    exact hv1 (hfpf v hv (by rw [h1]; simp))
  have hL1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  rw [hL1] at hxL1
  obtain ⟨hL1K, -⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  exact ⟨x, hxL1, E.k_le_hz (hL1K hxL1), hx3, hx1⟩

variable (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include hF

theorem fpf_of_three {x : G} (hxL : x ∈ l1 T L V) (hxH : x ∈ hz T V) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) {u : G} (hu : u ∈ fsuU T V) (hc : x * u * x⁻¹ * u⁻¹ ∈ fsuV1 T V) :
    u ∈ fsuV1 T V := by
  set h := hF.toHypF91 with hh
  obtain ⟨-, -, c, -, -, -, hcL, -, -, -, -, -, -, -, -, -, -, hfpf, -⟩ := E.exists_frame hF
  have hcx : c ∈ Subgroup.zpowers
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) (⟨x, hxH⟩ : ↥(hz T V))) := by
    rw [E.zpowers_eq_l1dot hxL hxH hx3 hx1]
    exact hcL
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hcx)
  have huU : u ∈ conjClosure V (hz T V) := E.fsuU_eq ▸ hu
  have h1 : rhoDot h (QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) (⟨x, hxH⟩ : ↥(hz T V)))
      (clsU h huU) = clsU h huU := by
    rw [QuotientGroup.mk'_apply, rhoDot_mk, rhoH_clsU_eq_iff]
    exact hc
  have h2 : ∀ m : ℕ, rhoDot h ((QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V))
      (⟨x, hxH⟩ : ↥(hz T V))) ^ m) (clsU h huU) = clsU h huU := by
    intro m
    induction m with
    | zero => rw [pow_zero, map_one, MulAut.one_apply]
    | succ m ih => rw [pow_succ, map_mul, MulAut.mul_apply, h1, ih]
  have h3 := h2 n
  rw [hn] at h3
  exact (clsU_eq_one_iff h huU).mp (hfpf _ h3)

theorem not_isLnBlock : ¬ IsLnBlock L 3 := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h := E.S.hyp
  rintro ⟨⟨-, -, ⟨hUQ, hU2⟩, -, -⟩, α, -, -, β, -, hβk, hβe⟩
  have h13322 := stmt13_3_2_two_of E.h1332
  obtain ⟨x, hxL1, hxH, hx3, hx1⟩ := E.exists_three
  have hxL : x ∈ L := ((oTwoUpper_le _).trans inf_le_left) hxL1
  have hUe := isElemAbelian_fsuU_of h hMod
  have hUc : ∀ a ∈ fsuU T V, ∀ b ∈ fsuU T V, a * b = b * a :=
    fun a ha b hb => F7.isElemAbelian_comm hUe ha hb
  have hU2' : ∀ a ∈ fsuU T V, a * a = 1 := fun a ha => by
    rw [← sq]
    exact F7.isElemAbelian_pow_eq_one hUe ha
  have hxU : x ∈ Subgroup.normalizer (fsuU T V : Set G) := hz_le_normalizer_U h hMod hxH
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hUH : fsuU T V ≤ hz T V := fun u hu => Subgroup.mem_centralizer_iff.mpr fun v hv =>
    hUc _ (hVU ((inf_le_left : fsuV1 T V ≤ V) hv)) _ hu
  have hUQH : fsuU T V ≤ pCoreOf 2 (hz T V) :=
    le_pCoreOf_of_le_normalizer 2 hUH (hz_le_normalizer_U h hMod)
      (B2F.isPGroup_of_isElemAbelian hUe)
  have hUT : fsuU T V ≤ T := hUQH.trans
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h E.t_le_hz))
  have hUC : fsuU T V ≤ Subgroup.centralizer (V : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => hUc _ (hVU hv) _ hu
  have hULT : fsuU T V ≤ pCoreOf 2 (L ⊔ T) := by
    rw [← hF.cT]
    exact le_inf hUT hUC
  have hTL := h.normalizes h13322
  have hLO : L ⊓ pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 L :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun l hl => mem_normalizer_inf_of_mem (Subgroup.le_normalizer hl)
        ((le_sup_left.trans (le_normalizer_pCoreOf 2 _)) hl))
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
  have hψO : ∀ u ∈ fsuU T V, x * u * x⁻¹ * u⁻¹ ∈ pCoreOf 2 L := by
    intro u hu
    refine hLO (Subgroup.mem_inf.mpr ⟨?_, hULT (mul_mem
      ((Subgroup.mem_normalizer_iff.mp hxU u).mp hu) (inv_mem hu))⟩)
    rw [show x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) by group]
    exact mul_mem hxL ((Subgroup.mem_normalizer_iff.mp (hTL (hUT hu)) _).mp (inv_mem hxL))
  have hψ2 : ∀ o ∈ pCoreOf 2 L, x * o * x⁻¹ * o⁻¹ ∈ blockU L := by
    intro o ho
    have hc := Subgroup.commutator_mem_commutator (show o ∈ blockQ L from ho) hxL
    rw [commutatorElement_def] at hc
    rw [show x * o * x⁻¹ * o⁻¹ = (o * x * o⁻¹ * x⁻¹)⁻¹ by group]
    exact inv_mem hc
  have hBc : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hUQ hb)).2 a
      (Subgroup.mem_inf.mp (hUQ ha)).1
  have hB2 : ∀ a ∈ blockU L, a * a = 1 := fun a ha => by rw [← sq]; exact hU2 a ha
  have hxB : x ∈ Subgroup.normalizer (blockU L : Set G) :=
    A3.sup_le_normalizer_commutator (blockQ L) L (Subgroup.mem_sup_right hxL)
  set ψ := commHom hUc hxU with hψ
  set cB := commHom hBc hxB with hcB
  set ψ3 := ψ.comp (ψ.comp ψ) with hψ3
  have hker : ∀ u : ↥(fsuU T V), ψ3 u = 1 → (u : G) ∈ fsuV1 T V := by
    intro u hu
    have hfix : ∀ w : ↥(fsuU T V), ψ (ψ w) = 1 → ψ w = 1 := by
      intro w hw
      apply Subtype.ext
      have h1 : x * ((ψ w : ↥(fsuU T V)) : G) * x⁻¹ * ((ψ w : ↥(fsuU T V)) : G)⁻¹ = 1 :=
        congrArg Subtype.val hw
      have h2 : x * ((ψ w : ↥(fsuU T V)) : G) * x⁻¹ = (ψ w : ↥(fsuU T V)) := by
        calc x * ((ψ w : ↥(fsuU T V)) : G) * x⁻¹ =
            x * ((ψ w : ↥(fsuU T V)) : G) * x⁻¹ * ((ψ w : ↥(fsuU T V)) : G)⁻¹ *
              (ψ w : ↥(fsuU T V)) := by group
          _ = _ := by rw [h1, one_mul]
      exact comm_eq_one_of_fix hUc hU2' hx3 hxU w.2 h2
    have hu1 := hfix u (hfix (ψ u) hu)
    apply E.fpf_of_three hF hxL1 hxH hx3 hx1 u.2
    have : x * (u : G) * x⁻¹ * (u : G)⁻¹ = 1 := congrArg Subtype.val hu1
    rw [this]
    exact one_mem _
  have hV1U : fsuV1 T V ≤ fsuU T V := (inf_le_left : fsuV1 T V ≤ V).trans hVU
  have hcardU : Nat.card ↥(fsuU T V) = 64 * Nat.card ↥(fsuV1 T V) := by
    have e := Subgroup.relIndex_mul_card (fsuV1 T V) (fsuU T V)
    rw [inf_eq_left.mpr hV1U, E.card_u hF] at e
    exact e.symm
  have hkerc : Nat.card ↥ψ3.ker ≤ Nat.card ↥(fsuV1 T V) := by
    rw [← Subgroup.card_map_of_injective (fsuU T V).subtype_injective]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨u, hu, rfl⟩
    exact hker u hu
  have hR64 : 64 ≤ Nat.card ↥ψ3.range := by
    have e := Subgroup.card_ker_mul_card_range ψ3
    rw [hcardU] at e
    have hpos : 0 < Nat.card ↥(fsuV1 T V) := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥ψ3.ker * Nat.card ↥ψ3.range < Nat.card ↥(fsuV1 T V) * 64 :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ hkerc) (Nat.mul_lt_mul_of_pos_left hlt hpos)
    omega
  have hsub : ψ3.range.map (fsuU T V).subtype ≤ cB.range.map (blockU L).subtype := by
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    have h2 : ((ψ (ψ u) : ↥(fsuU T V)) : G) ∈ blockU L := hψ2 _ (hψO _ u.2)
    exact ⟨cB ⟨_, h2⟩, ⟨⟨_, h2⟩, rfl⟩, rfl⟩
  have hle := Subgroup.card_le_of_le hsub
  rw [Subgroup.card_map_of_injective (fsuU T V).subtype_injective,
    Subgroup.card_map_of_injective (blockU L).subtype_injective] at hle
  set M : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
    (((α ⟨x, hxL⟩ : _) : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) with hM
  have hM3 : M ^ 3 = 1 := by
    have : (α ⟨x, hxL⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hxL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    rw [hM, ← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, this]
    rfl
  set S := Finset.univ.image fun v : Fin 3 → ZMod 2 => M.mulVec v + v with hS
  have hS4 := mat3_card_image M hM3
  have hβc : ∀ w : ↥(blockU L), Multiplicative.toAdd (β (cB w)) =
      M.mulVec (Multiplicative.toAdd (β w)) + Multiplicative.toAdd (β w) := by
    intro w
    have hxw : x * (w : G) * x⁻¹ ∈ blockU L := (Subgroup.mem_normalizer_iff.mp hxB w).mp w.2
    have e1 := hβe ⟨x, hxL⟩ w ⟨_, hxw⟩ rfl
    have hcw : cB w = ⟨_, hxw⟩ * w⁻¹ := Subtype.ext (by rw [hcB, coe_commHom]; simp)
    rw [hcw, map_mul, map_inv, toAdd_mul, toAdd_inv, e1, f2_neg_eq]
  have hinj : Function.Injective fun c : ↥cB.range => Multiplicative.toAdd (β c) := by
    rintro ⟨_, ⟨w, rfl⟩⟩ ⟨_, ⟨w', rfl⟩⟩ he
    simp only at he
    have he' : β (cB w) = β (cB w') := Multiplicative.toAdd.injective he
    have hzk : cB w * (cB w')⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, he', ← map_mul, mul_inv_cancel, map_one]
    rw [hβk, Subgroup.mem_subgroupOf] at hzk
    have hcz : x * ((cB (w * w'⁻¹) : ↥(blockU L)) : G) * x⁻¹ =
        ((cB (w * w'⁻¹) : ↥(blockU L)) : G) := by
      have hzL := (Subgroup.mem_inf.mp hzk).2
      rw [map_mul, map_inv]
      rw [← (Subgroup.mem_centralizer_iff.mp hzL x hxL).symm, mul_inv_cancel_right]
    have h1 := comm_eq_one_of_fix hBc hB2 hx3 hxB (w * w'⁻¹).2 hcz
    have h2 : cB (w * w'⁻¹) = 1 := Subtype.ext h1
    rw [map_mul, map_inv, mul_inv_eq_one] at h2
    exact Subtype.ext h2
  have hmapsto : ∀ c : ↥cB.range, Multiplicative.toAdd (β c) ∈ S := by
    rintro ⟨_, ⟨w, rfl⟩⟩
    rw [hS, Finset.mem_image]
    exact ⟨_, Finset.mem_univ _, (hβc w).symm⟩
  have hc4 : Nat.card ↥cB.range ≤ 4 := by
    have := Nat.card_le_card_of_injective (fun c : ↥cB.range =>
      (⟨Multiplicative.toAdd (β c), hmapsto c⟩ : ↥(S : Set (Fin 3 → ZMod 2))))
      (fun a b e => hinj (congrArg Subtype.val e))
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset] at this
    exact this.trans hS4
  omega

theorem normalizer_baum_le (hC137 : U3.C137Statement) :
    Subgroup.normalizer (baum (pCoreOf 2 (l1 T L V ⊔ T)) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h := E.S.hyp
  have h13322 := stmt13_3_2_two_of E.h1332
  have hL1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  rw [← hL1]
  rcases U3.stmt13_3_10_L32 E.h1332 E.h1222 E.h1334 hC137 h.hyp.h13 (h.hyp1223 h13322).irrPlus
      (Hyp147.inf_centralizer_eq_bot h h13322 hMod) h.hyp.linear with
    ⟨C, hCB, hC1, hCchar, hLTC⟩ | hblk
  · refine (normalizer_le_normalizer_of_characteristic hCB hCchar).trans ?_
    exact normalizer_le_normalizer_L h h13322 hC1
      ((pCoreOf_isPGroup 2 _).to_le (hCB.trans inf_le_left)) hLTC
  · exact absurd hblk (E.not_isLnBlock hF)

end Ctx7153

end CFSG.Quasithin.H13.L32A
