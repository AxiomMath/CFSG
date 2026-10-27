module

public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.H13.L32A768c
public import CFSG.Quasithin.H13.L32A770k

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem mat3_card_image : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M ^ 3 = 1 →
    (Finset.univ.image fun v : Fin 3 → ZMod 2 => M.mulVec v + v).card ≤ 4 := by
  decide +kernel

omit [Finite G] in
theorem comm_eq_one_of_fix {A : Subgroup G} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA2 : ∀ a ∈ A, a * a = 1) {x : G} (hx3 : x ^ 3 = 1)
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) {w : G} (hw : w ∈ A)
    (hfix : x * (x * w * x⁻¹ * w⁻¹) * x⁻¹ = x * w * x⁻¹ * w⁻¹) : x * w * x⁻¹ * w⁻¹ = 1 := by
  have hs : x * w * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hxA w).mp hw
  have ht : x * (x * w * x⁻¹) * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hxA _).mp hs
  have h2 : x * (x * w * x⁻¹) * x⁻¹ = w := by
    have e : x * (x * w * x⁻¹ * w⁻¹) * x⁻¹ =
        (x * (x * w * x⁻¹) * x⁻¹) * (x * w * x⁻¹)⁻¹ := by group
    rw [e] at hfix
    have e2 : x * (x * w * x⁻¹) * x⁻¹ = (x * w * x⁻¹) * w⁻¹ * (x * w * x⁻¹) := by
      calc x * (x * w * x⁻¹) * x⁻¹ =
          (x * (x * w * x⁻¹) * x⁻¹) * (x * w * x⁻¹)⁻¹ * (x * w * x⁻¹) := by group
        _ = (x * w * x⁻¹) * w⁻¹ * (x * w * x⁻¹) := by rw [hfix]
    rw [e2, mul_assoc, hAc _ (inv_mem hw) _ hs, ← mul_assoc, hA2 _ hs, one_mul]
    have := hA2 w hw
    calc w⁻¹ = w⁻¹ * (w * w) := by rw [this, mul_one]
      _ = w := by group
  have h3 : x * w * x⁻¹ = w := by
    calc x * w * x⁻¹ = x * (x * (x * w * x⁻¹) * x⁻¹) * x⁻¹ := by rw [h2]
      _ = x ^ 3 * w * (x ^ 3)⁻¹ := by rw [pow_three]; group
      _ = w := by rw [hx3]; group
  rw [h3, mul_inv_cancel]

theorem mem_u0_of_comm_of_three (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    {x : G} (hxK : x ∈ kz T V) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {u : G} (hu : u ∈ fsuU T V)
    (hc : x * u * x⁻¹ * u⁻¹ ∈ u0 T V) : u ∈ u0 T V := by
  obtain ⟨hKU, π, β, -, hπk, -, hβk, hβe⟩ := isL24Section_u0 h hMod h63
  have hxu : x * u * x⁻¹ ∈ fsuU T V := (Subgroup.mem_normalizer_iff.mp (hKU hxK) u).mp hu
  have hπ3 : π ⟨x, hxK⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxK⟩ : ↥(kz T V)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hπ1 : π ⟨x, hxK⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨x, hxK⟩ : ↥(kz T V)) ∈ π.ker := h1
    rw [hπk, Subgroup.mem_subgroupOf] at h2
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (kz T V)) ⟨x, h2⟩
    have hxn : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨hx3, hxn⟩
    rw [hcop.gcd_eq_one, pow_one] at this
    exact hx1 this
  have e1 := hβe ⟨x, hxK⟩ ⟨u, hu⟩ ⟨_, hxu⟩ rfl
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hcm : (⟨x * u * x⁻¹, hxu⟩ : ↥(fsuU T V)) =
      ⟨x * u * x⁻¹ * u⁻¹, hU0U hc⟩ * ⟨u, hu⟩ := Subtype.ext (by simp)
  have hc1 : β ⟨x * u * x⁻¹ * u⁻¹, hU0U hc⟩ = 1 := (l24_ker_iff hβk _).mpr hc
  rw [hcm, map_mul, hc1, one_mul] at e1
  have hfix := congrArg Multiplicative.toAdd e1
  rw [toAdd_ofAdd] at hfix
  have h3 := sl24_order_three _ hπ3 hπ1 (Multiplicative.toAdd (β ⟨u, hu⟩))
  rw [← hfix, ← hfix] at h3
  have h0 : Multiplicative.toAdd (β ⟨u, hu⟩) = 0 := by
    have key : ∀ v : Fin 2 → RuType.F4, v + v + v = 0 → v = 0 := by decide
    exact key _ h3
  have : β ⟨u, hu⟩ = 1 := Multiplicative.toAdd.injective h0
  exact (l24_ker_iff hβk _).mp this

omit [Finite G] in
@[expose] def commHom {A : Subgroup G} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {x : G}
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) : ↥A →* ↥A where
  toFun w := ⟨x * w * x⁻¹ * (w : G)⁻¹,
    mul_mem ((Subgroup.mem_normalizer_iff.mp hxA w).mp w.2) (inv_mem w.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    simp only [Subgroup.coe_mul, MulMemClass.mk_mul_mk]
    have hb : x * (b : G) * x⁻¹ * (b : G)⁻¹ ∈ A :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp hxA b).mp b.2) (inv_mem b.2)
    have h1 := hAc _ hb _ (inv_mem a.2)
    calc x * ((a : G) * b) * x⁻¹ * ((a : G) * b)⁻¹ =
        (x * a * x⁻¹) * ((x * (b : G) * x⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
      _ = (x * a * x⁻¹) * ((a : G)⁻¹ * (x * (b : G) * x⁻¹ * (b : G)⁻¹)) := by rw [h1]
      _ = _ := by group)

omit [Finite G] in
theorem coe_commHom {A : Subgroup G} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {x : G}
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) (w : ↥A) :
    ((commHom hAc hxA w : ↥A) : G) = x * w * x⁻¹ * (w : G)⁻¹ := rfl

theorem f2_neg_eq : ∀ v : Fin 3 → ZMod 2, -v = v := by
  decide

theorem not_isLnBlock (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) : ¬ IsLnBlock L 3 := by
  rintro ⟨⟨-, -, ⟨hUQ, hU2⟩, -, -⟩, α, -, -, β, -, hβk, hβe⟩
  have h13322 := stmt13_3_2_two_of h1332
  obtain ⟨x, hxL1, hx3, hfpf⟩ := exists_l1_fpf h hMod h1222 h1332 h1334
  obtain ⟨-, hV8, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  have hx1 : x ≠ 1 := by
    intro h1
    obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ∉ fsuV1 T V := by
      by_contra hno
      push Not at hno
      have := Subgroup.card_le_of_le (show V ≤ fsuV1 T V from hno)
      rw [hV8, hV1] at this
      omega
    exact hv1 (hfpf v hv (by rw [h1]; simp))
  have hxL : x ∈ L := ((oTwoRes_le _).trans inf_le_left) hxL1
  have hxK : x ∈ kz T V := l1_le_kz h hMod hxL1
  have hxH : x ∈ hz T V := oTwoUpper_le _ hxK
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
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h (T_le_hz h h63)))
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
  have hker : ∀ u : ↥(fsuU T V), ψ3 u = 1 → (u : G) ∈ u0 T V := by
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
    apply mem_u0_of_comm_of_three h hMod h63 hxK hx3 hx1 u.2
    have : x * (u : G) * x⁻¹ * (u : G)⁻¹ = 1 := congrArg Subtype.val hu1
    rw [this]
    exact one_mem _
  have hcardU : Nat.card ↥(fsuU T V) = 16 * Nat.card ↥(u0 T V) := by
    have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
    have e := Subgroup.relIndex_mul_card (u0 T V) (fsuU T V)
    rw [inf_eq_left.mpr hU0U, relIndex_u0 h hMod h63] at e
    exact e.symm
  have hkerc : Nat.card ↥ψ3.ker ≤ Nat.card ↥(u0 T V) := by
    rw [← Subgroup.card_map_of_injective (fsuU T V).subtype_injective]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨u, hu, rfl⟩
    exact hker u hu
  have hR16 : 16 ≤ Nat.card ↥ψ3.range := by
    have e := Subgroup.card_ker_mul_card_range ψ3
    rw [hcardU] at e
    have hpos : 0 < Nat.card ↥(u0 T V) := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥ψ3.ker * Nat.card ↥ψ3.range < Nat.card ↥(u0 T V) * 16 :=
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
    have hz : cB w * (cB w')⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, he', ← map_mul, mul_inv_cancel, map_one]
    rw [hβk, Subgroup.mem_subgroupOf] at hz
    have hcz : x * ((cB (w * w'⁻¹) : ↥(blockU L)) : G) * x⁻¹ =
        ((cB (w * w'⁻¹) : ↥(blockU L)) : G) := by
      have hzL := (Subgroup.mem_inf.mp hz).2
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

end CFSG.Quasithin.H13.L32A
