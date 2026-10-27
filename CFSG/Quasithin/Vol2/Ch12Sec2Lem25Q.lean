module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25P
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25N

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem25

variable {G : Type} [Group G]

structure PhiData (R V A : Subgroup G) (v₀ : G) : Prop where
  le : A ≤ V
  comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  index : (A.subgroupOf V).index = 2
  cent : R ≤ Subgroup.centralizer (A : Set G)
  norm : R ≤ Subgroup.normalizer (V : Set G)
  mem : v₀ ∈ V
  not_mem : v₀ ∉ A

namespace PhiData

variable {R V A : Subgroup G} {v₀ : G}

theorem mul_mem_iff (hD : PhiData R V A v₀) {v w : G} (hv : v ∈ V) (hw : w ∈ V) :
    v * w ∈ A ↔ (v ∈ A ↔ w ∈ A) := by
  have := Subgroup.mul_mem_iff_of_index_two hD.index (a := ⟨v, hv⟩) (b := ⟨w, hw⟩)
  simpa [Subgroup.mem_subgroupOf] using this

theorem comm_of_mem (hD : PhiData R V A v₀) {r a : G} (hr : r ∈ R) (ha : a ∈ A) :
    r * a = a * r :=
  (Subgroup.mem_centralizer_iff.mp (hD.cent hr) a ha).symm

theorem comm_mem (hD : PhiData R V A v₀) {r : G} (hr : r ∈ R) : r * v₀ * r⁻¹ * v₀⁻¹ ∈ A := by
  have hw : r * v₀ * r⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hD.norm hr) v₀).mp hD.mem
  have hwA : r * v₀ * r⁻¹ ∉ A := by
    intro h
    apply hD.not_mem
    have hc := hD.comm_of_mem (R.inv_mem hr) h
    have e : v₀ = r⁻¹ * (r * v₀ * r⁻¹) * r := by group
    rw [e, hc, mul_assoc, inv_mul_cancel, mul_one]
    exact h
  exact (hD.mul_mem_iff hw (V.inv_mem hD.mem)).mpr
    (iff_of_false hwA fun h => hD.not_mem (by simpa using A.inv_mem h))

@[expose] def phi (hD : PhiData R V A v₀) : ↥R →* ↥A where
  toFun r := ⟨(r : G) * v₀ * (r : G)⁻¹ * v₀⁻¹, hD.comm_mem r.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' r s := by
    apply Subtype.ext
    have hs := hD.comm_mem s.2
    have hr := hD.comm_mem r.2
    have hcomm : (r : G) * ((s : G) * v₀ * (s : G)⁻¹ * v₀⁻¹) =
        ((s : G) * v₀ * (s : G)⁻¹ * v₀⁻¹) * r := hD.comm_of_mem r.2 hs
    have hab := hD.comm _ (hD.le hs) _ (hD.le hr)
    change (r : G) * s * v₀ * ((r : G) * s)⁻¹ * v₀⁻¹ =
      ((r : G) * v₀ * (r : G)⁻¹ * v₀⁻¹) * ((s : G) * v₀ * (s : G)⁻¹ * v₀⁻¹)
    calc (r : G) * s * v₀ * ((r : G) * s)⁻¹ * v₀⁻¹ =
        (r : G) * ((s : G) * v₀ * (s : G)⁻¹ * v₀⁻¹) * (v₀ * (r : G)⁻¹ * v₀⁻¹) := by group
      _ = ((s : G) * v₀ * (s : G)⁻¹ * v₀⁻¹) * r * (v₀ * (r : G)⁻¹ * v₀⁻¹) := by rw [hcomm]
      _ = ((s : G) * v₀ * (s : G)⁻¹ * v₀⁻¹) * ((r : G) * v₀ * (r : G)⁻¹ * v₀⁻¹) := by group
      _ = _ := hab

theorem phi_apply (hD : PhiData R V A v₀) (r : ↥R) :
    ((hD.phi r : ↥A) : G) = (r : G) * v₀ * (r : G)⁻¹ * v₀⁻¹ := rfl

theorem mem_centralizer_of_comm (hD : PhiData R V A v₀) {r : G} (hr : r ∈ R)
    (h : r * v₀ = v₀ * r) : r ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  by_cases hvA : v ∈ A
  · exact (hD.comm_of_mem hr hvA).symm
  · have ha : v * v₀⁻¹ ∈ A := (hD.mul_mem_iff hv (V.inv_mem hD.mem)).mpr
      (iff_of_false hvA fun h' => hD.not_mem (by simpa using A.inv_mem h'))
    have e : v = (v * v₀⁻¹) * v₀ := by group
    rw [e, mul_assoc, ← h, ← mul_assoc, (hD.comm_of_mem hr ha).symm, mul_assoc]

theorem phi_eq_one_iff (hD : PhiData R V A v₀) (r : ↥R) :
    hD.phi r = 1 ↔ (r : G) ∈ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h
    have h1 : (r : G) * v₀ * (r : G)⁻¹ * v₀⁻¹ = 1 := congrArg Subtype.val h
    refine hD.mem_centralizer_of_comm r.2 ?_
    calc (r : G) * v₀ = (r : G) * v₀ * (r : G)⁻¹ * v₀⁻¹ * (v₀ * r) := by group
      _ = v₀ * r := by rw [h1, one_mul]
  · intro h
    apply Subtype.ext
    rw [phi_apply, ← Subgroup.mem_centralizer_iff.mp h v₀ hD.mem]
    simp

theorem comm_eq (hD : PhiData R V A v₀) {s w : G} (hs : s ∈ R) (hw : w ∈ V) (hwA : w ∉ A) :
    s * w * s⁻¹ * w⁻¹ = s * v₀ * s⁻¹ * v₀⁻¹ := by
  have ha : w * v₀⁻¹ ∈ A := (hD.mul_mem_iff hw (V.inv_mem hD.mem)).mpr
    (iff_of_false hwA fun h' => hD.not_mem (by simpa using A.inv_mem h'))
  set a := w * v₀⁻¹ with ha_def
  have hwa : w = a * v₀ := by rw [ha_def]; group
  have hsa : s * a = a * s := hD.comm_of_mem hs ha
  have hd := hD.comm_mem hs
  have hda : a * (s * v₀ * s⁻¹ * v₀⁻¹) = (s * v₀ * s⁻¹ * v₀⁻¹) * a :=
    hD.comm _ (hD.le ha) _ (hD.le hd)
  rw [hwa]
  calc s * (a * v₀) * s⁻¹ * (a * v₀)⁻¹ = (s * a) * v₀ * s⁻¹ * v₀⁻¹ * a⁻¹ := by group
    _ = (a * s) * v₀ * s⁻¹ * v₀⁻¹ * a⁻¹ := by rw [hsa]
    _ = a * (s * v₀ * s⁻¹ * v₀⁻¹) * a⁻¹ := by group
    _ = (s * v₀ * s⁻¹ * v₀⁻¹) * a * a⁻¹ := by rw [hda]
    _ = s * v₀ * s⁻¹ * v₀⁻¹ := by group

theorem comm_conj (hD : PhiData R V A v₀) {x r : G} (hxR : x ∈ Subgroup.normalizer (R : Set G))
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxA : x ∈ Subgroup.normalizer (A : Set G))
    (hr : r ∈ R) :
    (x * r * x⁻¹) * v₀ * (x * r * x⁻¹)⁻¹ * v₀⁻¹ = x * (r * v₀ * r⁻¹ * v₀⁻¹) * x⁻¹ := by
  have hs : x * r * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hxR r).mp hr
  have hw : x * v₀ * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxV v₀).mp hD.mem
  have hwA : x * v₀ * x⁻¹ ∉ A := fun h => hD.not_mem ((Subgroup.mem_normalizer_iff.mp hxA v₀).mpr h)
  rw [← hD.comm_eq hs hw hwA]
  group

end PhiData

theorem card_eq_card_inf_mul {X : Type*} [Group X] {H K : Subgroup G} (f : ↥H →* X)
    (hker : ∀ x : ↥H, f x = 1 ↔ (x : G) ∈ K) :
    Nat.card H = Nat.card ↥(K ⊓ H) * Nat.card f.range := by
  have hk : f.ker = K.subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker]
  rw [← Subgroup.card_ker_mul_card_range f, hk, ← Subgroup.subgroupOf_map_subtype,
    Subgroup.card_map_of_injective H.subtype_injective]

theorem T_le_normalizer_V (h1222 : Stmt12_2_2) [Finite G] {T L V : Subgroup G}
    (hH : Hyp1223 G T L V) : T ≤ Subgroup.normalizer (V : Set G) := by
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  obtain ⟨-, -, hall⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨-, hTV, -, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  exact hTV

theorem inf_V_le_RR [Finite G] {T L V H P U I : Subgroup G} {h : G} {n p : ℕ}
    (hH : Hyp1223 G T L V) (hC : Config12_2_24 T L V H P U I h n p) : U ⊓ V ≤ RR T U := by
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  obtain ⟨hHs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hUe, -, -, -, -, hUO, -⟩ := hC
  have hUT : U ≤ (S : Subgroup G) :=
    hUO.trans (A7.pCoreOf_le_of_le_normalizer S (hHs.1.1.trans Subgroup.le_normalizer))
  intro a ha
  refine ⟨hUT ha.1, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
  exact congrArg Subtype.val (hUe.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha.1⟩)

theorem exists_phiData (h1222 : Stmt12_2_2) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hC : Config12_2_24 T L V H P U I h n p) :
    ∃ v₀ : G, PhiData (RR T U) V (U ⊓ V) v₀ := by
  have hidx : ((U ⊓ V).subgroupOf V).index = 2 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hidx, -⟩ := hC
    exact hidx
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  obtain ⟨v₀, hv₀V, hv₀A⟩ : ∃ v₀ ∈ V, v₀ ∉ U ⊓ V := by
    by_contra hno
    push Not at hno
    have htop : (U ⊓ V).subgroupOf V = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨v, hv⟩ -
      exact Subgroup.mem_subgroupOf.mpr (hno v hv)
    rw [htop, Subgroup.index_top] at hidx
    omega
  refine ⟨v₀, inf_le_right, fun a ha b hb => ?_, hidx,
    inf_le_right.trans (Subgroup.centralizer_le inf_le_left),
    inf_le_left.trans (T_le_normalizer_V h1222 hH), hv₀V, hv₀A⟩
  exact congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem exists_mem_U_not_mem_centralizer [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hC : Config12_2_24 T L V H P U I h n p) :
    ∃ u ∈ U, u ∉ Subgroup.centralizer (V : Set G) := by
  classical
  obtain ⟨-, -, hn, hVn, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hidx, ⟨hcommV, htv⟩,
    -⟩ := hC
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have : IsMulCommutative ↥V := hcommV
  have hV2 : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (hVe.2 w w.2)
  set W := (U ⊓ V).subgroupOf V with hWdef
  have hidx' : W.index = 2 := hidx
  have hWne : W ≠ ⊥ := by
    intro hbot
    have h1 := W.card_mul_index
    rw [hidx', hbot, Subgroup.card_bot] at h1
    have h2 : Nat.card ↥V = 2 ^ n := hVn
    rw [h2] at h1
    rcases hn with rfl | rfl | rfl <;> norm_num at h1
  obtain ⟨⟨a, haW⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
  have ha1' : a ≠ 1 := fun h' => ha1 (Subtype.ext h')
  obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Lem24.transvAxis_ne_bot hV2 hidx' haW ha1')
  have hcU : c ∈ autOn U V := htv ▸ hc
  obtain ⟨x, hxU, hxc⟩ := hcU
  refine ⟨x, Subgroup.mem_subgroupOf.mp hxU, fun hxV => hc1 (Subtype.ext ?_)⟩
  show c = 1
  rw [← hxc]
  refine MulEquiv.ext fun w => Subtype.ext ?_
  change (x : G) * w * (x : G)⁻¹ = w
  rw [← Subgroup.mem_centralizer_iff.mp hxV w w.2, mul_inv_cancel_right]

theorem phi_surjective
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn4 : n = 4) {v₀ : G}
    (hD : PhiData (RR T U) V (U ⊓ V) v₀) : Function.Surjective hD.phi := by
  obtain ⟨-, -, hYN, -, -⟩ := yn_data h331 h1222 h323 h1216 h1220 hH hNE hC (by omega)
  have hYV : YY L U V ≤ Subgroup.normalizer (V : Set G) :=
    ((oTwoUpper_le _).trans inf_le_left).trans (le_normalizer_of_hyp1223 hH)
  set B : Subgroup G := hD.phi.range.map (U ⊓ V).subtype with hB
  have hBA : B ≤ U ⊓ V := Subgroup.map_subtype_le _
  have hBne : B ≠ ⊥ := by
    obtain ⟨u, huU, huV⟩ := exists_mem_U_not_mem_centralizer hH hC
    have huR : u ∈ RR T U := by
      obtain ⟨-, -, -, hc4, -⟩ := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H P U I h
        n p hH hNE hC
      have hU : U ≤ RR T U := by
        rw [show RR T U = U ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) from by
          obtain ⟨-, -, hc3, -⟩ := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H P U I h
            n p hH hNE hC
          exact hc3]
        exact le_sup_left
      exact hU huU
    intro hbot
    have h1 : ((hD.phi ⟨u, huR⟩ : ↥(U ⊓ V)) : G) ∈ B := ⟨_, ⟨⟨u, huR⟩, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact huV ((hD.phi_eq_one_iff ⟨u, huR⟩).mp (Subtype.ext h1))
  have hYB : YY L U V ≤ Subgroup.normalizer (B : Set G) := by
    intro y hy
    refine mem_normalizer_of_conj_mem fun b hb => ?_
    obtain ⟨_, ⟨r, rfl⟩, rfl⟩ := hb
    have hyr : y * (r : G) * y⁻¹ ∈ RR T U :=
      (Subgroup.mem_normalizer_iff.mp (hYN hy) r).mp r.2
    refine ⟨_, ⟨⟨_, hyr⟩, rfl⟩, ?_⟩
    show ((hD.phi ⟨_, hyr⟩ : ↥(U ⊓ V)) : G) = y * ((hD.phi r : ↥(U ⊓ V)) : G) * y⁻¹
    rw [PhiData.phi_apply, PhiData.phi_apply]
    exact hD.comm_conj (hYN hy) (hYV hy) (YY_le_normalizer hy) r.2
  have hBeq := eq_inf_V_of_le h1222 h1220 hH hNE hC hn4 hBA hBne hYB
  intro a
  have ha : (a : G) ∈ B := by rw [hBeq]; exact a.2
  obtain ⟨_, ⟨r, rfl⟩, hr⟩ := ha
  exact ⟨r, Subtype.ext hr⟩

theorem CTL_facts
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) :
    T ⊓ Subgroup.centralizer (L : Set G) ≤ RR T U ∧
      T ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.centralizer (V : Set G) ∧
      T ⊓ Subgroup.centralizer (L : Set G) ≤
        Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) ∧
      (U ⊓ V) ⊓ (T ⊓ Subgroup.centralizer (L : Set G)) = ⊥ ∧
      Nat.card (RR T U) = Nat.card U * Nat.card ↥(T ⊓ Subgroup.centralizer (L : Set G)) := by
  obtain ⟨-, -, hc3, hc4, -⟩ := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H P U I h
    n p hH hNE hC
  have hVL := V_le_L' hH
  have h1 : T ⊓ Subgroup.centralizer (L : Set G) ≤ RR T U := by
    show _ ≤ T ⊓ Subgroup.centralizer (U : Set G)
    rw [hc3]
    exact le_sup_right
  have h2 : T ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.centralizer (V : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le hVL)
  have h3 : T ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) :=
    h2.trans (Subgroup.centralizer_le inf_le_right)
  have h4 : (U ⊓ V) ⊓ (T ⊓ Subgroup.centralizer (L : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxU, -⟩, -, hxL⟩
    have : x ∈ U ⊓ Subgroup.centralizer (L : Set G) := ⟨hxU, hxL⟩
    rw [hc4] at this
    exact this
  have hKU : T ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.centralizer (U : Set G) :=
    fun c hc => (h1 hc).2
  have hUK : U ⊓ (T ⊓ Subgroup.centralizer (L : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, -, hxL⟩
    have : x ∈ U ⊓ Subgroup.centralizer (L : Set G) := ⟨hxU, hxL⟩
    rw [hc4] at this
    exact this
  refine ⟨h1, h2, h3, h4, ?_⟩
  show Nat.card ↥(T ⊓ Subgroup.centralizer (U : Set G)) = _
  rw [hc3, card_sup_eq_mul hKU hUK]

theorem inf_centralizer_V_eq
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn4 : n = 4) {v₀ : G}
    (hD : PhiData (RR T U) V (U ⊓ V) v₀) :
    RR T U ⊓ Subgroup.centralizer (V : Set G) = (U ⊓ V) ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ∧
      Nat.card (RR T U) = Nat.card ↥(RR T U ⊓ Subgroup.centralizer (V : Set G)) * 8 := by
  obtain ⟨hKR, hKV, hKA, hAK, hR⟩ := CTL_facts h331 h1222 h323 h1216 h1220 hH hNE hC
  have hA : Nat.card ↥(U ⊓ V) = 8 := by rw [card_inf_V hC, hn4]; norm_num
  have hU : Nat.card U = 8 * 8 := by rw [card_U hC, hn4]; norm_num
  have hsurj := phi_surjective h331 h1222 h323 h1216 h1220 hH hNE hC hn4 hD
  have hRc := card_eq_card_inf_mul (K := Subgroup.centralizer (V : Set G)) hD.phi
    hD.phi_eq_one_iff
  rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hA, inf_comm] at hRc
  refine ⟨?_, hRc⟩
  have hle : (U ⊓ V) ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ≤
      RR T U ⊓ Subgroup.centralizer (V : Set G) := by
    refine sup_le (le_inf (inf_V_le_RR hH hC) fun a ha => ?_) (le_inf hKR hKV)
    exact Subgroup.mem_centralizer_iff.mpr fun b hb => hD.comm b hb a ha.2
  have hcard := card_sup_eq_mul hKA hAK
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hcard, hA]
  have : Nat.card ↥(RR T U ⊓ Subgroup.centralizer (V : Set G)) * 8 =
      8 * Nat.card ↥(T ⊓ Subgroup.centralizer (L : Set G)) * 8 := by
    rw [← hRc, hR, hU]
    ring
  omega

theorem card_RR_centralizer_three
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn4 : n = 4) {y : G} (hyY : y ∈ YY L U V)
    (hy : orderOf y = 3) :
    Nat.card ↥(RR T U ⊓ Subgroup.centralizer ({y} : Set G)) * 16 = Nat.card (RR T U) := by
  obtain ⟨v₀, hD⟩ := exists_phiData h1222 hH hC
  obtain ⟨hKR, hKV, hKA, hAK, hR⟩ := CTL_facts h331 h1222 h323 h1216 h1220 hH hNE hC
  obtain ⟨hSeq, hRS⟩ := inf_centralizer_V_eq h331 h1222 h323 h1216 h1220 hH hNE hC hn4 hD
  obtain ⟨-, -, -, -, -, -, -, hc8, -⟩ := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H
    P U I h n p hH hNE hC
  obtain ⟨-, -, hYN, -, -⟩ := yn_data h331 h1222 h323 h1216 h1220 hH hNE hC (by omega)
  have hsurj := phi_surjective h331 h1222 h323 h1216 h1220 hH hNE hC hn4 hD
  have hA : Nat.card ↥(U ⊓ V) = 8 := by rw [card_inf_V hC, hn4]; norm_num
  have hU : Nat.card U = 8 * 8 := by rw [card_U hC, hn4]; norm_num
  have hAy := card_inf_V_centralizer_three h1222 h1220 hH hNE hC hn4 hyY hy
  have hy3 : y ^ 3 = 1 := hy ▸ pow_orderOf_eq_one y
  have hyL : y ∈ L := (oTwoUpper_le _).trans inf_le_left hyY
  have hyR : y ∈ Subgroup.normalizer ((RR T U : Subgroup G) : Set G) := hYN hyY
  have hyV : y ∈ Subgroup.normalizer (V : Set G) :=
    ((oTwoUpper_le _).trans inf_le_left).trans (le_normalizer_of_hyp1223 hH) hyY
  have hyA : y ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) := YY_le_normalizer hyY
  have hRab : ∀ a ∈ RR T U, ∀ b ∈ RR T U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hc8.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have hKy : T ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.centralizer ({y} : Set G) :=
    fun c hc => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hc.2 y hyL).symm
  have hSy : RR T U ⊓ Subgroup.centralizer (V : Set G) ⊓ Subgroup.centralizer ({y} : Set G) =
      (U ⊓ V ⊓ Subgroup.centralizer ({y} : Set G)) ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [hSeq]
    apply le_antisymm
    · rintro s ⟨hs, hsy⟩
      obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup_centralizer hKA hs
      have hcy : c * y = y * c := Subgroup.mem_centralizer_singleton_iff.mp (hKy hc)
      have hsy' : a * c * y = y * (a * c) := Subgroup.mem_centralizer_singleton_iff.mp hsy
      have hay : a * y = y * a := by
        have e : a * y * c = y * a * c := by
          calc a * y * c = a * (c * y) := by rw [mul_assoc, ← hcy]
            _ = a * c * y := by group
            _ = y * (a * c) := hsy'
            _ = y * a * c := by group
        exact mul_right_cancel e
      exact Subgroup.mul_mem_sup ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr hay⟩ hc
    · exact sup_le (inf_le_inf_right _ le_sup_left) (le_inf le_sup_right hKy)
  have hSyc : Nat.card ↥(RR T U ⊓ Subgroup.centralizer (V : Set G) ⊓
      Subgroup.centralizer ({y} : Set G)) =
        2 * Nat.card ↥(T ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [hSy, card_sup_eq_mul (hKA.trans (Subgroup.centralizer_le inf_le_left)) ?_, hAy]
    rw [eq_bot_iff]
    intro x hx
    rw [← hAK]
    exact ⟨hx.1.1, hx.2⟩
  set f := hD.phi.comp (Subgroup.inclusion
    (inf_le_left : RR T U ⊓ Subgroup.centralizer ({y} : Set G) ≤ RR T U)) with hf
  have hfker : ∀ x : ↥(RR T U ⊓ Subgroup.centralizer ({y} : Set G)),
      f x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V : Set G) := fun x => hD.phi_eq_one_iff _
  have hcardRy := card_eq_card_inf_mul f hfker
  have hrange : f.range.map (U ⊓ V).subtype = U ⊓ V ⊓ Subgroup.centralizer ({y} : Set G) := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
      refine ⟨(f r).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hry : y * (r : G) * y⁻¹ = r := by
        rw [← Subgroup.mem_centralizer_singleton_iff.mp r.2.2, mul_inv_cancel_right]
      have e := hD.comm_conj hyR hyV hyA r.2.1
      rw [hry] at e
      show (r : G) * v₀ * (r : G)⁻¹ * v₀⁻¹ * y = y * ((r : G) * v₀ * (r : G)⁻¹ * v₀⁻¹)
      calc (r : G) * v₀ * (r : G)⁻¹ * v₀⁻¹ * y =
          y * (r * v₀ * (r : G)⁻¹ * v₀⁻¹) * y⁻¹ * y := by rw [← e]
        _ = y * ((r : G) * v₀ * (r : G)⁻¹ * v₀⁻¹) := by group
    · rintro a ⟨haA, hay⟩
      obtain ⟨r, hr⟩ := hsurj ⟨a, haA⟩
      have hra : (r : G) * v₀ * (r : G)⁻¹ * v₀⁻¹ = a := congrArg Subtype.val hr
      have hay' : y * a * y⁻¹ = a := by
        rw [(Subgroup.mem_centralizer_singleton_iff.mp hay).symm, mul_inv_cancel_right]
      set r₁ := y * (r : G) * y⁻¹ with hr₁
      have hr₁R : r₁ ∈ RR T U := (Subgroup.mem_normalizer_iff.mp hyR r).mp r.2
      set r₂ := y * r₁ * y⁻¹ with hr₂
      have hr₂R : r₂ ∈ RR T U := (Subgroup.mem_normalizer_iff.mp hyR r₁).mp hr₁R
      have hφ₁ : r₁ * v₀ * r₁⁻¹ * v₀⁻¹ = a := by
        rw [hr₁, hD.comm_conj hyR hyV hyA r.2, hra, hay']
      have hφ₂ : r₂ * v₀ * r₂⁻¹ * v₀⁻¹ = a := by
        rw [hr₂, hD.comm_conj hyR hyV hyA hr₁R, hφ₁, hay']
      set r' : G := (r : G) * r₁ * r₂ with hr'
      have hr'R : r' ∈ RR T U := (RR T U).mul_mem ((RR T U).mul_mem r.2 hr₁R) hr₂R
      have hyr₂ : y * r₂ * y⁻¹ = r := by
        rw [hr₂, hr₁]
        have hyyy : y * (y * y) = 1 := by simpa [pow_succ, mul_assoc] using hy3
        calc y * (y * (y * (r : G) * y⁻¹) * y⁻¹) * y⁻¹ =
            (y * (y * y)) * r * (y * (y * y))⁻¹ := by group
          _ = r := by rw [hyyy]; group
      have hr'y : y * r' * y⁻¹ = r' := by
        calc y * r' * y⁻¹ = (y * (r : G) * y⁻¹) * (y * r₁ * y⁻¹) * (y * r₂ * y⁻¹) := by
              rw [hr']; group
          _ = r₁ * r₂ * r := by rw [hyr₂]
          _ = r * (r₁ * r₂) := hRab _ ((RR T U).mul_mem hr₁R hr₂R) _ r.2
          _ = r' := by rw [hr']; group
      have hr'C : r' ∈ Subgroup.centralizer ({y} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc r' * y = y * r' * y⁻¹ * y := by rw [hr'y]
          _ = y * r' := by group
      refine ⟨_, ⟨⟨r', hr'R, hr'C⟩, rfl⟩, ?_⟩
      have hmul : (f ⟨r', hr'R, hr'C⟩ : G) = (hD.phi r : G) * (hD.phi ⟨r₁, hr₁R⟩ : G) *
          (hD.phi ⟨r₂, hr₂R⟩ : G) := by
        have e : (⟨r', hr'R⟩ : ↥(RR T U)) = r * ⟨r₁, hr₁R⟩ * ⟨r₂, hr₂R⟩ := rfl
        show ((hD.phi ⟨r', hr'R⟩ : ↥(U ⊓ V)) : G) = _
        rw [e, map_mul, map_mul]
        rfl
      show (f ⟨r', hr'R, hr'C⟩ : G) = a
      rw [hmul, PhiData.phi_apply, PhiData.phi_apply, PhiData.phi_apply, hra]
      show a * (r₁ * v₀ * r₁⁻¹ * v₀⁻¹) * (r₂ * v₀ * r₂⁻¹ * v₀⁻¹) = a
      rw [hφ₁, hφ₂]
      have ha2 : a * a = 1 := by rw [← pow_two]; exact hVe.2 a haA.2
      rw [ha2, one_mul]
  have hfr : Nat.card f.range = 2 := by
    rw [← hAy, ← hrange, Subgroup.card_map_of_injective (U ⊓ V).subtype_injective]
  rw [hcardRy, hfr]
  have e1 : Subgroup.centralizer (V : Set G) ⊓ (RR T U ⊓ Subgroup.centralizer ({y} : Set G)) =
      RR T U ⊓ Subgroup.centralizer (V : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [← inf_assoc, inf_comm (Subgroup.centralizer (V : Set G))]
  rw [e1, hSyc, hRS]
  have : Nat.card ↥(RR T U ⊓ Subgroup.centralizer (V : Set G)) * 8 =
      8 * 8 * Nat.card ↥(T ⊓ Subgroup.centralizer (L : Set G)) := by rw [← hRS, hR, hU]
  omega

theorem mem_normalizer_Y_of_fix (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) [Finite G]
    {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hH : Hyp1223 G T L V)
    (hNE : NoEscape12_2_13 L V) (hC : Config12_2_24 T L V H P U I h n p) {c a : G}
    (hcR : c ∈ Subgroup.normalizer ((RR T U : Subgroup G) : Set G)) (haA : a ∈ U ⊓ V)
    (ha1 : a ≠ 1) (hca : c * a = a * c) :
    c ∈ Subgroup.normalizer (L : Set G) ∧ c ∈ Subgroup.normalizer (V : Set G) ∧
      c ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) ∧
      c ∈ Subgroup.normalizer ((YY L U V : Subgroup G) : Set G) := by
  obtain ⟨hcL, hcV⟩ := mem_normalizer_of_fix h1222 h323 hH hNE haA.2 ha1 hca
  have hcA : c ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) := by
    have := Subgroup.inf_normalizer_le_normalizer_inf ⟨hcR, hcV⟩
    rwa [inf_V_eq h1222 hH hC] at this
  exact ⟨hcL, hcV, hcA, mem_normalizer_Y hcL hcA⟩

theorem exists_fix_of_card
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn4 : n = 4) {c : G}
    (hcard : Nat.card ↥(RR T U ⊓ Subgroup.centralizer ({c} : Set G)) * 4 = Nat.card (RR T U)) :
    ∃ a ∈ U ⊓ V, a ≠ 1 ∧ c * a = a * c := by
  obtain ⟨-, -, -, -, -, -, -, hc8, -⟩ := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H
    P U I h n p hH hNE hC
  have hA : Nat.card ↥(U ⊓ V) = 8 := by rw [card_inf_V hC, hn4]; norm_num
  by_contra hno
  push Not at hno
  have hRab : ∀ a ∈ RR T U, ∀ b ∈ RR T U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hc8.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAR := inf_V_le_RR hH hC
  have hKA : RR T U ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) :=
    fun x hx => Subgroup.mem_centralizer_iff.mpr fun a ha => hRab a (hAR ha) x hx.1
  have hAK : U ⊓ V ⊓ (RR T U ⊓ Subgroup.centralizer ({c} : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨haA, -, hac⟩
    by_contra ha1
    exact hno a haA ha1 (Subgroup.mem_centralizer_singleton_iff.mp hac).symm
  have hcard' := card_sup_eq_mul hKA hAK
  have hle : Nat.card ↥(U ⊓ V ⊔ RR T U ⊓ Subgroup.centralizer ({c} : Set G)) ≤
      Nat.card (RR T U) := Subgroup.card_le_of_le (sup_le hAR inf_le_left)
  rw [hcard', hA] at hle
  have hpos := Nat.card_pos (α := ↥(RR T U ⊓ Subgroup.centralizer ({c} : Set G)))
  omega

theorem eq_one_of_centralizes
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn4 : n = 4) {x : G}
    (hxR : x ∈ Subgroup.normalizer ((RR T U : Subgroup G) : Set G)) (hx : Odd (orderOf x))
    (hxA : ∀ a ∈ U ⊓ V, x * a = a * x) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v₀, hD⟩ := exists_phiData h1222 hH hC
  obtain ⟨hKR, hKV, hKA, hAK, -⟩ := CTL_facts h331 h1222 h323 h1216 h1220 hH hNE hC
  obtain ⟨hSeq, -⟩ := inf_centralizer_V_eq h331 h1222 h323 h1216 h1220 hH hNE hC hn4 hD
  obtain ⟨-, -, -, -, -, -, -, -, hc9, -⟩ := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V
    H P U I h n p hH hNE hC
  have hA : Nat.card ↥(U ⊓ V) = 8 := by rw [card_inf_V hC, hn4]; norm_num
  obtain ⟨⟨a, haA⟩, ha1⟩ : ∃ a : ↥(U ⊓ V), a ≠ 1 := by
    by_contra hno
    push Not at hno
    have : Nat.card ↥(U ⊓ V) = 1 := Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun a b => by rw [hno a, hno b]⟩, ⟨1⟩⟩
    omega
  have ha1' : a ≠ 1 := fun h' => ha1 (Subtype.ext h')
  obtain ⟨hxL, hxV, hxA', -⟩ := mem_normalizer_Y_of_fix h1222 h323 hH hNE hC hxR haA ha1'
    (hxA a haA)
  have hxCL := mem_centralizer_L_of_fix h331 h1222 h323 h1216 h1220 hH hNE hC hxL hxV hx hxA
  have hR2 : IsPGroup 2 (RR T U) := hH.sylow.1.to_le inf_le_left
  have hxS : ∀ d ∈ RR T U ⊓ Subgroup.centralizer (V : Set G), x * d * x⁻¹ = d := by
    intro d hd
    rw [hSeq] at hd
    obtain ⟨a', ha', c, hc, rfl⟩ := exists_mul_of_mem_sup_centralizer hKA hd
    have hxa' : x * a' * x⁻¹ = a' := by rw [hxA a' ha', mul_inv_cancel_right]
    have hxc : x * c * x⁻¹ = c := by
      by_cases hc1 : c = 1
      · rw [hc1]; group
      have hxcT : x * c * x⁻¹ ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
        refine ⟨((Subgroup.mem_normalizer_iff.mp hxR c).mp (hKR hc)).1, ?_⟩
        show x * c * x⁻¹ ∈ Subgroup.centralizer (L : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have h1 : l * x = x * l := Subgroup.mem_centralizer_iff.mp hxCL l hl
        have h2 : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc.2 l hl
        have h3 : l * x⁻¹ = x⁻¹ * l := by
          calc l * x⁻¹ = x⁻¹ * (x * l) * x⁻¹ := by group
            _ = x⁻¹ * (l * x) * x⁻¹ := by rw [h1]
            _ = x⁻¹ * l := by group
        calc l * (x * c * x⁻¹) = x * (l * c) * x⁻¹ := by
              rw [← mul_assoc, ← mul_assoc, h1]; group
          _ = x * c * (l * x⁻¹) := by rw [h2]; group
          _ = x * c * x⁻¹ * l := by rw [h3]; group
      have hxc1 : x * c * x⁻¹ ≠ 1 := fun h' => hc1 (by
        calc c = x⁻¹ * (x * c * x⁻¹) * x := by group
          _ = 1 := by rw [h']; group)
      exact eq_of_card_le_two hc9 hxcT hc hxc1 hc1
    calc x * (a' * c) * x⁻¹ = (x * a' * x⁻¹) * (x * c * x⁻¹) := by group
      _ = a' * c := by rw [hxa', hxc]
  have hxC : x ∈ Subgroup.centralizer ((RR T U : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hs : x * r * x⁻¹ ∈ RR T U := (Subgroup.mem_normalizer_iff.mp hxR r).mp hr
    set d := x * r * x⁻¹ * r⁻¹ with hd
    have hdR : d ∈ RR T U := (RR T U).mul_mem hs ((RR T U).inv_mem hr)
    have hdV : d ∈ Subgroup.centralizer (V : Set G) := by
      have e1 := hD.comm_conj hxR hxV hxA' hr
      have hcomm : x * (r * v₀ * r⁻¹ * v₀⁻¹) * x⁻¹ = r * v₀ * r⁻¹ * v₀⁻¹ := by
        rw [hxA _ (hD.comm_mem hr), mul_inv_cancel_right]
      rw [hcomm] at e1
      have hphi : hD.phi ⟨d, hdR⟩ = 1 := by
        have e2 : (⟨d, hdR⟩ : ↥(RR T U)) = ⟨_, hs⟩ * (⟨r, hr⟩ : ↥(RR T U))⁻¹ := rfl
        rw [e2, map_mul, map_inv]
        apply mul_inv_eq_one.mpr
        exact Subtype.ext e1
      exact (hD.phi_eq_one_iff ⟨d, hdR⟩).mp hphi
    have hxd : x * d * x⁻¹ = d := hxS d ⟨hdR, hdV⟩
    have hd2 : ∃ k : ℕ, d ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hR2 ⟨d, hdR⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hdr : x * r * x⁻¹ = d * r := by rw [hd]; group
    have := conj_eq_of_odd hdr hxd hd2 hx
    calc r * x = (x * r * x⁻¹) * x := by rw [this]
      _ = x * r := by group
  have hxRR := centralizer_R_le hH hC hxC
  obtain ⟨k, hk⟩ := hR2 ⟨x, hxRR⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hx)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hk'))

end Lem25

end CFSG.Quasithin.H13
