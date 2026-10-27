module

public import CFSG.Quasithin.Vol2.Ch3Sec2Lem322Eight
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.Background.F9Comp
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative

section FixedMod

variable {G : Type} [Group G] {V C J : Subgroup G}

@[expose] def conjOn (hJV : J ≤ Subgroup.normalizer (V : Set G)) (j : ↥J) : ↥V ≃* ↥V where
  toFun v := ⟨j * v * j⁻¹, (Subgroup.mem_normalizer_iff.mp (hJV j.2) v).mp v.2⟩
  invFun v := ⟨(j : G)⁻¹ * v * j, by
    have := (Subgroup.mem_normalizer_iff.mp (hJV (J.inv_mem j.2)) v).mp v.2
    simpa using this⟩
  left_inv v := Subtype.ext (by simp [mul_assoc])
  right_inv v := Subtype.ext (by simp [mul_assoc])
  map_mul' u v := Subtype.ext (by simp [mul_assoc])

theorem coe_conjOn (hJV : J ≤ Subgroup.normalizer (V : Set G)) (j : ↥J) (v : ↥V) :
    ((conjOn hJV j v : ↥V) : G) = j * v * j⁻¹ := rfl

theorem map_conjOn (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hJC : J ≤ Subgroup.normalizer (C : Set G)) (j : ↥J) :
    (C.subgroupOf V).map (conjOn hJV j : ↥V →* ↥V) = C.subgroupOf V := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hJC j.2) v).mp hv
  · intro v hv
    refine ⟨(conjOn hJV j).symm v, ?_, (conjOn hJV j).apply_symm_apply v⟩
    have := (Subgroup.mem_normalizer_iff.mp (hJC (J.inv_mem j.2)) v).mp hv
    show (j : G)⁻¹ * (v : G) * j ∈ C
    simpa using this

@[expose] noncomputable def quotAct [(C.subgroupOf V).Normal]
    (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hJC : J ≤ Subgroup.normalizer (C : Set G)) : ↥J →* MulAut (↥V ⧸ C.subgroupOf V) where
  toFun j := QuotientGroup.congr _ _ (conjOn hJV j) (map_conjOn hJV hJC j)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H v =>
      show (QuotientGroup.mk (conjOn hJV 1 v) : ↥V ⧸ C.subgroupOf V) = QuotientGroup.mk v
      congr 1
      exact Subtype.ext (by simp [coe_conjOn])
  map_mul' a b := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H v =>
      show (QuotientGroup.mk (conjOn hJV (a * b) v) : ↥V ⧸ C.subgroupOf V) =
        QuotientGroup.mk (conjOn hJV a (conjOn hJV b v))
      congr 1
      exact Subtype.ext (by simp [coe_conjOn, mul_assoc])

theorem exists_fixed_mod [Finite G] (hV2 : IsPGroup 2 V) (hJ2 : IsPGroup 2 J) (hCV : C < V)
    (hJV : J ≤ Subgroup.normalizer (V : Set G)) (hJC : J ≤ Subgroup.normalizer (C : Set G))
    (hVC : V ≤ Subgroup.normalizer (C : Set G)) :
    ∃ v ∈ V, v ∉ C ∧ ∀ j ∈ J, j * v * j⁻¹ * v⁻¹ ∈ C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCn : (C.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCV.le).mpr hVC
  let Q := ↥V ⧸ C.subgroupOf V
  let _ : MulAction ↥J Q := MulAction.compHom Q (quotAct hJV hJC)
  have hsmul : ∀ (j : ↥J) (v : ↥V), j • (QuotientGroup.mk v : Q) =
      QuotientGroup.mk (conjOn hJV j v) := fun _ _ => rfl
  have hJ2' : IsPGroup 2 ↥J := hJ2
  have hQ2 : IsPGroup 2 Q := hV2.to_quotient _
  obtain ⟨w, hwV, hwC⟩ := Set.exists_of_ssubset hCV
  have hQnt : Nontrivial Q := by
    refine ⟨⟨QuotientGroup.mk ⟨w, hwV⟩, 1, fun h => hwC ?_⟩⟩
    have := (QuotientGroup.eq_one_iff (N := C.subgroupOf V) ⟨w, hwV⟩).mp h
    exact this
  have h2Q : 2 ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := hQ2.nontrivial_iff_card.mp hQnt
    rw [hn.2]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn.1)
  have h1 : (1 : Q) ∈ MulAction.fixedPoints ↥J Q := fun j => by
    show quotAct hJV hJC j 1 = 1
    exact map_one _
  obtain ⟨b, hb, hb1⟩ := hJ2'.exists_fixed_point_of_prime_dvd_card_of_fixed_point Q h2Q h1
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨v, v.2, fun hvC => hb1 ?_, fun j hj => ?_⟩
  · exact ((QuotientGroup.eq_one_iff (N := C.subgroupOf V) v).mpr hvC).symm
  · have h := hb ⟨j, hj⟩
    rw [hsmul] at h
    have h2 := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h2
    have h3 : (j * (v : G) * j⁻¹)⁻¹ * v ∈ C := h2
    have h4 := (Subgroup.mem_normalizer_iff.mp (hVC v.2) _).mp (C.inv_mem h3)
    have e : (v : G) * ((j * (v : G) * j⁻¹)⁻¹ * v)⁻¹ * (v : G)⁻¹ =
        j * (v : G) * j⁻¹ * (v : G)⁻¹ := by group
    rw [e] at h4
    exact h4

end FixedMod

section IrrPlus

variable {G : Type} [Group G] {L V J : Subgroup G}

theorem conj_mem_inf_centralizer {g x : G} (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (hx : x ∈ V ⊓ Subgroup.centralizer (L : Set G)) :
    g * x * g⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hgV x).mp hx.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : g⁻¹ * l * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgL) l).mp hl
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ hl'
  calc l * (g * x * g⁻¹) = g * ((g⁻¹ * l * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * l * g)) * g⁻¹ := by rw [hc]
    _ = g * x * g⁻¹ * l := by group

theorem mem_normalizer_inf_centralizer {g : G} (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_inf_centralizer hgV hgL, fun h => ?_⟩
  have := conj_mem_inf_centralizer (Subgroup.inv_mem _ hgV) (Subgroup.inv_mem _ hgL) h
  simpa [mul_assoc] using this

theorem conj_comm_of_commutator_le (hc : ⁅J, L⁆ ≤ Subgroup.centralizer (V : Set G)) {j l v : G}
    (hj : j ∈ J) (hl : l ∈ L) (hv : v ∈ V) :
    j * (l * v * l⁻¹) * j⁻¹ = l * (j * v * j⁻¹) * l⁻¹ := by
  have hcV : j⁻¹ * l⁻¹ * j * l ∈ Subgroup.centralizer (V : Set G) := by
    have := hc (Subgroup.commutator_mem_commutator (J.inv_mem hj) (L.inv_mem hl))
    rwa [commutatorElement_def, inv_inv, inv_inv] at this
  have hcv := (Subgroup.mem_centralizer_iff.mp hcV v hv).symm
  calc j * (l * v * l⁻¹) * j⁻¹
      = l * j * ((j⁻¹ * l⁻¹ * j * l) * v) * (j⁻¹ * l⁻¹ * j * l)⁻¹ * j⁻¹ * l⁻¹ := by group
    _ = l * j * (v * (j⁻¹ * l⁻¹ * j * l)) * (j⁻¹ * l⁻¹ * j * l)⁻¹ * j⁻¹ * l⁻¹ := by rw [hcv]
    _ = l * (j * v * j⁻¹) * l⁻¹ := by group

theorem le_centralizer_of_commutator_le [Finite G] (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hV2 : IsPGroup 2 V) (hJ2 : IsPGroup 2 J) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hJV : J ≤ Subgroup.normalizer (V : Set G)) (hJL : J ≤ Subgroup.normalizer (L : Set G))
    (hVL : ⁅V, L⁆ = V) (hlt : V ⊓ Subgroup.centralizer (L : Set G) < V)
    (hirr : ∀ W : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ W → W ≤ V →
      L ≤ Subgroup.normalizer (W : Set G) → W = V ⊓ Subgroup.centralizer (L : Set G) ∨ W = V)
    (hc : ⁅J, L⁆ ≤ Subgroup.centralizer (V : Set G)) :
    J ≤ Subgroup.centralizer (V : Set G) := by
  set C := V ⊓ Subgroup.centralizer (L : Set G) with hC
  have hJC : J ≤ Subgroup.normalizer (C : Set G) := fun j hj =>
    mem_normalizer_inf_centralizer (hJV hj) (hJL hj)
  have hLC : L ≤ Subgroup.normalizer (C : Set G) := fun l hl =>
    mem_normalizer_inf_centralizer (hLV hl) (Subgroup.le_normalizer hl)
  have hVC : V ≤ Subgroup.normalizer (C : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hVc v hv x hx.1, mul_inv_cancel_right]
      exact hx
    · intro hx
      have hxV : x ∈ V := by
        have h1 : v⁻¹ * (v * x * v⁻¹) * v ∈ V :=
          V.mul_mem (V.mul_mem (V.inv_mem hv) hx.1) hv
        simpa [mul_assoc] using h1
      rwa [hVc v hv x hxV, mul_inv_cancel_right] at hx
  let W : Subgroup G :=
    { carrier := {v | v ∈ V ∧ ∀ j ∈ J, j * v * j⁻¹ * v⁻¹ ∈ C}
      one_mem' := ⟨V.one_mem, fun j _ => by simp⟩
      mul_mem' := fun {u v} hu hv => ⟨V.mul_mem hu.1 hv.1, fun j hj => by
        have hq : j * v * j⁻¹ * v⁻¹ ∈ V :=
          V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hJV hj) v).mp hv.1) (V.inv_mem hv.1)
        have hcm := hVc u⁻¹ (V.inv_mem hu.1) _ hq
        have e : j * (u * v) * j⁻¹ * (u * v)⁻¹ =
            (j * u * j⁻¹ * u⁻¹) * (j * v * j⁻¹ * v⁻¹) := by
          calc j * (u * v) * j⁻¹ * (u * v)⁻¹ =
                (j * u * j⁻¹) * ((j * v * j⁻¹ * v⁻¹) * u⁻¹) := by group
            _ = (j * u * j⁻¹) * (u⁻¹ * (j * v * j⁻¹ * v⁻¹)) := by rw [← hcm]
            _ = (j * u * j⁻¹ * u⁻¹) * (j * v * j⁻¹ * v⁻¹) := by group
        rw [e]
        exact C.mul_mem (hu.2 j hj) (hv.2 j hj)⟩
      inv_mem' := fun {v} hv => ⟨V.inv_mem hv.1, fun j hj => by
        have h1 := (Subgroup.mem_normalizer_iff.mp (hVC (V.inv_mem hv.1)) _).mp
          (C.inv_mem (hv.2 j hj))
        have e : v⁻¹ * (j * v * j⁻¹ * v⁻¹)⁻¹ * v⁻¹⁻¹ = j * v⁻¹ * j⁻¹ * v⁻¹⁻¹ := by group
        rw [e] at h1
        exact h1⟩ }
  have hmemW : ∀ v, v ∈ W ↔ v ∈ V ∧ ∀ j ∈ J, j * v * j⁻¹ * v⁻¹ ∈ C := fun _ => Iff.rfl
  have hCW : C ≤ W := fun c hc' => (hmemW c).mpr ⟨hc'.1, fun j hj =>
    C.mul_mem ((Subgroup.mem_normalizer_iff.mp (hJC hj) c).mp hc') (C.inv_mem hc')⟩
  have hWV : W ≤ V := fun v hv => ((hmemW v).mp hv).1
  have hLW1 : ∀ l ∈ L, ∀ n ∈ W, l * n * l⁻¹ ∈ W := by
    intro l hl n hn
    obtain ⟨hnV, hnJ⟩ := (hmemW n).mp hn
    refine (hmemW _).mpr ⟨(Subgroup.mem_normalizer_iff.mp (hLV hl) n).mp hnV, fun j hj => ?_⟩
    have h1 := conj_comm_of_commutator_le hc hj hl hnV
    have e : j * (l * n * l⁻¹) * j⁻¹ * (l * n * l⁻¹)⁻¹ = l * (j * n * j⁻¹ * n⁻¹) * l⁻¹ := by
      rw [h1]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hLC hl) _).mp (hnJ j hj)
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨hLW1 l hl n, fun h => ?_⟩
    have := hLW1 l⁻¹ (L.inv_mem hl) _ h
    simpa [mul_assoc] using this
  obtain ⟨w, hwV, hwC, hw⟩ := exists_fixed_mod hV2 hJ2 hlt hJV hJC hVC
  have hWne : W ≠ C := fun h => hwC (h ▸ ((hmemW w).mpr ⟨hwV, hw⟩))
  have hWeq : W = V := (hirr W hCW hWV hLW).resolve_left hWne
  have hδ : ∀ v ∈ V, ∀ j ∈ J, j * v * j⁻¹ * v⁻¹ ∈ C := fun v hv j hj =>
    ((hmemW v).mp (hWeq.symm ▸ hv)).2 j hj
  intro j hj
  have key : ⁅V, L⁆ ≤ Subgroup.centralizer ({j} : Set G) := by
    rw [Subgroup.commutator_le]
    intro w hw l hl
    have ha := hδ w hw j hj
    have haV : j * w * j⁻¹ * w⁻¹ ∈ V := ha.1
    have haL := Subgroup.mem_centralizer_iff.mp ha.2 l hl
    have hxV : ⁅w, l⁆ ∈ V := by
      have h2 : w * (l * w⁻¹ * l⁻¹) ∈ V :=
        V.mul_mem hw ((Subgroup.mem_normalizer_iff.mp (hLV hl) _).mp (V.inv_mem hw))
      rw [commutatorElement_def]
      simpa [mul_assoc] using h2
    have h1 := conj_comm_of_commutator_le hc hj hl (V.inv_mem hw)
    have hcm := hVc _ haV _ hxV
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhj : h = j := hh
    rw [hhj]
    have e1 : j * ⁅w, l⁆ * j⁻¹ = (j * w * j⁻¹) * (j * (l * w⁻¹ * l⁻¹) * j⁻¹) := by
      rw [commutatorElement_def]
      group
    have e2 : l * (j * w⁻¹ * j⁻¹) * l⁻¹ =
        (l * w⁻¹ * l⁻¹) * (l * (j * w * j⁻¹ * w⁻¹)⁻¹ * l⁻¹) := by group
    have e3 : l * (j * w * j⁻¹ * w⁻¹)⁻¹ * l⁻¹ = (j * w * j⁻¹ * w⁻¹)⁻¹ := by
      generalize j * w * j⁻¹ * w⁻¹ = a at haL ⊢
      have h3 : a⁻¹ * l = l * a⁻¹ := by
        calc a⁻¹ * l = a⁻¹ * (l * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * l) * a⁻¹ := by rw [haL]
          _ = l * a⁻¹ := by group
      calc l * a⁻¹ * l⁻¹ = a⁻¹ * l * l⁻¹ := by rw [h3]
        _ = a⁻¹ := by group
    have e4 : j * ⁅w, l⁆ * j⁻¹ = (j * w * j⁻¹ * w⁻¹) * ⁅w, l⁆ * (j * w * j⁻¹ * w⁻¹)⁻¹ := by
      rw [e1, h1, e2, e3, commutatorElement_def]
      group
    have e5 : (j * w * j⁻¹ * w⁻¹) * ⁅w, l⁆ * (j * w * j⁻¹ * w⁻¹)⁻¹ = ⁅w, l⁆ := by
      rw [hcm, mul_inv_cancel_right]
    calc j * ⁅w, l⁆ = j * ⁅w, l⁆ * j⁻¹ * j := by group
      _ = ⁅w, l⁆ * j := by rw [e4, e5]
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : v ∈ ⁅V, L⁆ := by rw [hVL]; exact hv
  exact (Subgroup.mem_centralizer_iff.mp (key hv') j rfl).symm

end IrrPlus

section Main

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem omegaOneCenter_le_self' (T : Subgroup G) : quasithinOmegaOneCenter T ≤ T :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1.1

omit [Finite G] in
theorem le_centralizer_omegaOneCenter' (T : Subgroup G) :
    T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  Subgroup.le_centralizer_iff.mp ((Subgroup.closure_le _).mpr fun _ hz => hz.1.2)

theorem stmt12_2_9_one (h331 : Stmt3_3_1) (hH : Hyp1223 G T L V)
    (hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  set Z := quasithinOmegaOneCenter T with hZ
  set X := Z ⊓ Subgroup.centralizer (L : Set G) with hX
  have hXp : IsPGroup 2 X := hH.sylow.1.to_le (inf_le_left.trans (omegaOneCenter_le_self' T))
  obtain ⟨⟨-, -, huniq⟩, -⟩ :=
    (h331 G T hH.simple hH.nonabelian hH.qtke hH.sylow).2 L hH.maximal hH.quasisimple
  rw [hH.conjClosure_eq] at huniq
  obtain ⟨N, hNmax, hNle⟩ := exists_maxTwoLocal_ge (L := Subgroup.normalizer (X : Set G))
    ⟨X, hZL, hXp, rfl⟩
  have hLX : L ≤ Subgroup.centralizer (X : Set G) := Subgroup.le_centralizer_iff.mp inf_le_right
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := fun t ht =>
    mem_normalizer_inf_centralizer
      (Subgroup.centralizer_le_normalizer _ (le_centralizer_omegaOneCenter' T ht))
      (hH.normalizes ht)
  have hLTN : L ⊔ T ≤ N := sup_le
    ((hLX.trans (Subgroup.centralizer_le_normalizer _)).trans hNle) (hTX.trans hNle)
  rw [← huniq N hNmax hLTN]
  exact (Subgroup.centralizer_le fun x hx => (inf_le_left : X ≤ Z) hx).trans
    ((Subgroup.centralizer_le_normalizer _).trans hNle)

omit [Finite G] in
private theorem pCoreOf_subgroupOf_self (L : Subgroup G) :
    (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := CFSG.openPCoreOf_subgroupOf 2 L

theorem stmt12_2_9_two
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (hH : Hyp1223 G T L V)
    (hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (L : Set G)) :
    L = ⁅L, thompsonJ T⁆ := by
  obtain ⟨⟨hmax, hle, huniq⟩, -, ⟨H₀, hH₀⟩, -, -⟩ :=
    (h331 G T hH.simple hH.nonabelian hH.qtke hH.sylow).2 L hH.maximal hH.quasisimple
  rw [hH.conjClosure_eq] at hmax hle huniq hH₀
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, hab, -⟩ := hall V hH.irrPlus
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hV0 : conjClosure V T = V := conjClosure_eq_self_of_normalizes hTV
  have hQ : pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (V : Set G) := by
    have := (stmt3_2_2_eight_proved G T L V hH.fsu).2.2
    rwa [hH.conjClosure_eq, hV0] at this
  have hperf : L = oTwoUpper L := (hH.faithful.2.1 _ (oTwoUpper_le L)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le L)).mpr
      (le_normalizer_oTwoUpper L))
    fun _ hx => exists_pow_mem_oTwoUpper L hx).symm
  have h318 : Hyp318 T (Subgroup.normalizer (L : Set G)) L V :=
    { inM := ⟨hmax, hH.normalizes⟩
      nonempty := ⟨H₀, hH₀⟩
      perfect := hperf
      le_M := Subgroup.le_normalizer
      normal := le_rfl
      unique := ⟨⟨hmax, hle⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
      reduced := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mpr ⟨hVLT, hred⟩
      centralizer := hQ }
  have hJ : ¬ thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
    rcases theorem318_three hC58 h317 hH.simple hH.nonabelian hH.qtke hH.sylow h318 with
      ⟨hJ, -⟩ | ⟨-, hZ, -⟩
    · exact hJ
    · exfalso
      apply hH₀.2.1
      exact (Subgroup.le_centralizer_iff.mp ((hZ H₀ hH₀).trans inf_le_right)).trans hCZ
  have hJT : thompsonJ T ≤ T := iSup₂_le fun A hA => hA.1
  have hJL : thompsonJ T ≤ Subgroup.normalizer (L : Set G) := hJT.trans hH.normalizes
  have hcc : L ∈ cComp (L ⊔ T) := hH.faithful.1.2.1
  by_contra hne
  rcases cComp_commutator_dichotomy_of_le hcc (hJT.trans le_sup_right) with ⟨-, hsolv⟩ | hconj
  · apply hJ
    refine le_inf hJT ?_
    have hLJL : ⁅L, thompsonJ T⁆ ≤ L := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_right.mp hJL
    have hq' : CFSG.IsQuasisimple (↥L ⧸ (pCoreOf 2 L).subgroupOf L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq (pCoreOf_subgroupOf_self L).symm) hH.quasisimple
    have hD := commutator_le_pCoreOf_of_solvable hq' hLJL
      (Subgroup.normalizer_commutator_ge_left L (thompsonJ T)) hsolv
    have hJQ : ⁅thompsonJ T, L⁆ ≤ pCoreOf 2 L :=
      commutator_le_of_commutator_commutator_le
        (hJL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) (perfect_of_mem_cComp hcc) hD
    have hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := by
      have := pCoreOf_le_pCoreOf_of_isSubnormal (subnormal_of_mem_cComp hcc)
      rw [hQ] at this
      exact this.trans inf_le_right
    have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩)
    exact le_centralizer_of_commutator_le hVc (hH.sylow.1.to_le hVT) (hH.sylow.1.to_le hJT)
      hH.irrPlus.2.2.1 (hJT.trans hTV) hJL hH.irrPlus.2.2.2.1 hH.irrPlus.2.2.2.2.1
      hH.irrPlus.2.2.2.2.2.1 (hJQ.trans hO2)
  · exact hne (hconj.trans (conjClosure_eq_self_of_normalizes hJL)).symm

theorem stmt12_2_9_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (hC58 : TheoremC58) (h317 : AS317Sylow) : Stmt12_2_9 := fun _ _ _ _ _ _ hH =>
  ⟨stmt12_2_9_one h331 hH, stmt12_2_9_two h331 h1222 hC58 h317 hH⟩

end Main

end CFSG.Quasithin.H13
