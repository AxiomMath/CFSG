module

public import CFSG.Quasithin.H13.L32NLem14323a
public import CFSG.Quasithin.H13.L32NLem14332h
public import CFSG.Quasithin.H13.L32NLem14332d
public import CFSG.Quasithin.H13.L32NSp4Defs
public import CFSG.Quasithin.H13.L32NSp4Model

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

namespace L14323

variable {G : Type} [Group G]

section Img

variable {U : Subgroup G} (D : HatModelU U)

theorem img_mono {K K' : Subgroup G} (h : K ≤ K') : D.img K ≤ D.img K' :=
  Subgroup.map_mono fun _ hx => h hx

theorem img_le_sp (K : Subgroup G) : D.img K ≤ KGCert.spGroup D.B := by
  intro γ hγ
  obtain ⟨x, -, hxN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
  exact fun v w => L128A.HatU.B_rho D ⟨x, hxN⟩ v w

theorem isPGroup_img {p : ℕ} {K : Subgroup G} (hK : IsPGroup p ↥K)
    (hKN : K ≤ Subgroup.normalizer (U : Set G)) : IsPGroup p ↥(D.img K) :=
  (hK.of_equiv (Subgroup.subgroupOfEquivOfLe hKN).symm).map D.ρ

end Img

structure Ctx (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g a c : G)
    (D : HatModelU (fsuU T V)) : Prop where
  hyp : Hyp14310One G T L V
  plane : IsL32NPlane T V V₂
  setting : Setting1282One G T L V 3 (fsuV1 T V) V₂
  gP : g ∈ p128 T L V
  gN : g ∉ l32nH T V
  d4 : Module.finrank (ZMod 2) D.V = 4
  aV₂ : a ∈ V₂
  a1 : a ∉ fsuV1 T V
  cV : c ∈ V
  c2 : c ∉ V₂
  V_U : V ≤ fsuU T V
  V_comm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x
  V_sq : ∀ x ∈ V, x * x = 1
  card_V1 : Nat.card ↥(fsuV1 T V) = 2
  VZ : V ⊓ centerOf (fsuU T V) = fsuV1 T V
  hatV : D.hat V = D.hat (l32nE T V V₂ g)
  card_hatV : Nat.card ↥(D.hat V) = 4
  relIdx : (D.img (CFSG.conjugate (centerOf (fsuU T V)) g)).relIndex
    (D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2
  zU_fix : ∀ x ∈ D.img (CFSG.conjugate (centerOf (fsuU T V)) g), ∀ v ∈ D.hat V, x v = v
  lt_H : (l32nH T V ⊓ Subgroup.normalizer (L : Set G)) ⊔ l32nCHat T V < l32nH T V
  TH : T ≤ l32nH T V
  TV : T ≤ Subgroup.normalizer (V : Set G)
  TL : T ≤ Subgroup.normalizer (L : Set G)
  LV : L ≤ Subgroup.normalizer (V : Set G)
  T2 : IsPGroup 2 ↥T
  Todd : Odd ((D.img T).relIndex (D.img (l32nH T V)))
  zUg_le : CFSG.conjugate (centerOf (fsuU T V)) g ≤ l32nH T V
  Wg_le : CFSG.conjugate (l32nW T V V₂) g ≤ l32nH T V
  rot : ∃ l ∈ L, l ^ 3 = 1 ∧ l ∈ l32nH T V ∧ l * a * l⁻¹ = c
  g101 : G101Hyp D.B (D.img (Subgroup.normalizer (fsuV1 T V : Set G))) (D.π a)
    (D.hat (l32nE T V V₂ g)) (D.img (CFSG.conjugate (l32nW T V V₂) g))
    (D.img (CFSG.conjugate (centerOf (fsuU T V)) g))
  g112 : G11.G112ConclusionFix D.B (D.img (Subgroup.normalizer (fsuV1 T V : Set G)))
    (D.img (CFSG.conjugate (l32nW T V V₂) g))
  zU_ne : fsuV1 T V < centerOf (fsuU T V) →
    D.img (CFSG.conjugate (centerOf (fsuU T V)) g) ≠ ⊥
  quad : centerOf (fsuU T V) = fsuV1 T V → ∃ q : D.V → ZMod 2,
    (∀ u ∈ fsuU T V, q (D.π u) = 0 ↔ u ^ 2 = 1) ∧ (∀ v w, q (v + w) = q v + q w + D.B v w) ∧
      ∀ γ ∈ D.img (l32nH T V), ∀ v, q (γ v) = q v

theorem exists_ctx [Finite G] (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h1288 : Lemma12_8_8_two)
    (h12811 : Lemma12_8_11) (h12811h : Lemma12_8_11_hat) (h12813 : Lemma12_8_13)
    (hG112 : G11.TheoremG112Fix) {T L V : Subgroup G} (h : Hyp14310One G T L V)
    {V₂ : Subgroup G} {g : G} (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V)
    (hgN : g ∉ l32nH T V) (D : HatModelU (fsuU T V)) (hd : Module.finrank (ZMod 2) D.V = 4) :
    ∃ a c : G, Ctx G T L V V₂ g a c D := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  have hs := h.setting1282One h13322 hV hV₂
  obtain ⟨hVe, hV8, hLTV, hV1, -⟩ := hV G T L V h.hyp h.fsu
  obtain ⟨⟨hVE, hV4⟩, ⟨hrel, hfix⟩, hlt⟩ := lemma14323Parts_of_inputs h1332 h1334 h1222 h12213
    h12811 h12811h h12813 G T L V h V₂ g hV₂ hgP hgN D hd
  have hV₂4 : Nat.card V₂ = 4 := hV₂.1.2.1
  have hlt12 : fsuV1 T V < V₂ := lt_of_le_of_ne hV₂.2 fun he => by
    rw [he] at hV1; omega
  obtain ⟨a, haV₂, ha1⟩ := IsConcreteLE.exists_of_lt hlt12
  have hlt2 : V₂ < V := lt_of_le_of_ne hV₂.1.1 fun he => by
    rw [he] at hV₂4; omega
  obtain ⟨c, hcV, hc2⟩ := IsConcreteLE.exists_of_lt hlt2
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hVsq : ∀ x ∈ V, x * x = 1 := fun x hx => by rw [← pow_two]; exact hVe.2 x hx
  have hTH : T ≤ l32nH T V := h.le_l32nH hV
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hLTV
  have hTL : T ≤ Subgroup.normalizer (L : Set G) :=
    (h1332 G T L h.hyp.h13 L h.hyp.h13.faithful).2.1.1
  have hTodd : Odd ((D.img T).relIndex (D.img (l32nH T V))) := by
    have hdvd := L14332.relIndex_img_dvd D hTH (L14332.l32nH_le_normalizer_fsuU T V)
    have hsyl := (h.isSylowTwoOf_l32nH hV).2.2
    have hodd : Odd (T.relIndex (l32nH T V)) := Nat.odd_iff.mpr (by
      rcases Nat.even_or_odd (T.relIndex (l32nH T V)) with he | ho
      · exact absurd (even_iff_two_dvd.mp he) hsyl
      · exact Nat.odd_iff.mp ho)
    exact Odd.of_dvd_nat hodd hdvd
  have hgN₂ : g ∈ Subgroup.normalizer (V₂ : Set G) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hgP.2 V₂) ⟨2, le_rfl, hV₂.1⟩
  have hWg : CFSG.conjugate (l32nW T V V₂) g ≤ l32nH T V :=
    (L14332.conj_le_centralizer_of_le inf_le_right hV₂.2 hgN₂).trans
      (Subgroup.centralizer_le_normalizer _)
  have hzUg := L14332.conj_zU_le h12813 hs hgP hgN
  obtain ⟨hg101, -, hg112⟩ := lemma12_8_12_hat_of h1222 h12213 hG112 G T L V 3 (fsuV1 T V) V₂ hs
    g hgP hgN a haV₂ ha1 D
  have hrot : ∃ l ∈ L, l ^ 3 = 1 ∧ l ∈ l32nH T V ∧ l * a * l⁻¹ = c := by
    obtain ⟨_, S⟩ := L14332.exists_setting h1332 h1334 h1222 h hV₂
    obtain ⟨z, -, -, hz, hz1, -⟩ := S.exists_basis
    have haV : a ∈ V := hV₂.1.1 haV₂
    have hzV₂ : z ∈ V₂ := hV₂.2 hz
    obtain ⟨l, hlL, hl3, hlz, hla, -⟩ := S.exists_rot (Subgroup.mem_inf.mp hz).1 haV hcV
      (fun he => ha1 (by rw [he]; exact one_mem _)) (fun he => hc2 (by rw [he]; exact one_mem _))
      (fun he => ha1 (by rw [he]; exact hz)) (fun he => hc2 (by rw [he]; exact hzV₂))
      (fun he => hc2 (by rw [← he]; exact haV₂))
      (fun he => hc2 (by rw [he]; exact V₂.mul_mem hzV₂ haV₂))
    exact ⟨l, hlL, hl3, S.mem_g1 hz hz1 hlz, hla⟩
  have hzU : fsuV1 T V < centerOf (fsuU T V) →
      D.img (CFSG.conjugate (centerOf (fsuU T V)) g) ≠ ⊥ := by
    intro hlt' hbot
    obtain ⟨-, -, h3, -⟩ := h12813 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN
    apply h3 hlt'
    intro ζ hζ
    have hζH : ζ ∈ l32nH T V := hzUg hζ
    have hζN := L14332.l32nH_le_normalizer_fsuU T V hζH
    have h1 : D.ρ ⟨ζ, hζN⟩ = 1 := by
      have hmem := L128A.HatU.rho_mem_img D hζ hζN
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    exact (L14332.rho_eq_one_iff_mem hζH hζN).mp h1
  have hquad : centerOf (fsuU T V) = fsuV1 T V → ∃ q : D.V → ZMod 2,
      (∀ u ∈ fsuU T V, q (D.π u) = 0 ↔ u ^ 2 = 1) ∧
        (∀ v w, q (v + w) = q v + q w + D.B v w) ∧
        ∀ γ ∈ D.img (l32nH T V), ∀ v, q (γ v) = q v := by
    intro hZ
    obtain ⟨-, -, -, hq⟩ := h1288 G T L V 3 (fsuV1 T V) V₂ hs D
    refine hq (L14332.frattiniOf_eq_bot_of_sq (L14332.zU_comm _) fun y hy => ?_)
    have hy' : y ∈ centerOf (fsuU T V) := hy
    rw [hZ] at hy'
    exact hVsq y (Subgroup.mem_inf.mp hy').1
  exact ⟨a, c,
    { hyp := h, plane := hV₂, setting := hs, gP := hgP, gN := hgN, d4 := hd, aV₂ := haV₂,
      a1 := ha1, cV := hcV, c2 := hc2, V_U := hVU, V_comm := hVcomm, V_sq := hVsq,
      card_V1 := hV1, VZ := lemma12_8_8_three h1222 h12213 hs, hatV := hVE,
      card_hatV := hV4, relIdx := hrel, zU_fix := hfix, lt_H := hlt, TH := hTH, TV := hTV,
      TL := hTL, LV := le_sup_left.trans hLTV, T2 := h.fsu.sylow.1, Todd := hTodd,
      zUg_le := hzUg,
      Wg_le := hWg, rot := hrot, g101 := hg101, g112 := hg112, zU_ne := hzU,
      quad := hquad }⟩

namespace Ctx

variable [Finite G] {T L V V₂ : Subgroup G} {g a c : G} {D : HatModelU (fsuU T V)}
variable (C : Ctx G T L V V₂ g a c D)
include C

theorem dvd_card :
    10 ∣ Nat.card ↥(D.img (l32nH T V)) ∨ 18 ∣ Nat.card ↥(D.img (l32nH T V)) := by
  have hd := C.d4
  rcases C.g112 with (h | h | h | h | h | h | h | h | h | h | h | h | h) | h | h
  all_goals first
    | exact h.2
    | (exfalso; have := h.1; omega)

theorem aV : a ∈ V := C.plane.1.1 C.aV₂

theorem aU : a ∈ fsuU T V := C.V_U C.aV

theorem cU : c ∈ fsuU T V := C.V_U C.cV

theorem pi_a_mem : D.π a ∈ D.hat V := L128A.HatU.π_mem_hat D C.aV C.aU

theorem pi_c_mem : D.π c ∈ D.hat V := L128A.HatU.π_mem_hat D C.cV C.cU

theorem pi_a_ne : D.π a ≠ 0 := by
  intro h0
  have haZ := (L128A.HatU.π_eq_zero_iff D C.aU).mp h0
  apply C.a1
  rw [← C.VZ]
  exact ⟨C.aV, haZ⟩

theorem pi_c_ne : D.π c ≠ 0 := by
  intro h0
  have hcZ := (L128A.HatU.π_eq_zero_iff D C.cU).mp h0
  apply C.c2
  have : c ∈ fsuV1 T V := by rw [← C.VZ]; exact ⟨C.cV, hcZ⟩
  exact C.plane.2 this

theorem pi_a_ne_c : D.π a ≠ D.π c := by
  intro he
  have hz := (D.π_eq_iff a C.aU c C.cU).mp he
  have hV : a⁻¹ * c ∈ V := V.mul_mem (V.inv_mem C.aV) C.cV
  have h1 : a⁻¹ * c ∈ fsuV1 T V := by rw [← C.VZ]; exact ⟨hV, hz⟩
  apply C.c2
  rw [show c = a * (a⁻¹ * c) by group]
  exact V₂.mul_mem C.aV₂ (C.plane.2 h1)

theorem B_ac : D.B (D.π a) (D.π c) = 0 :=
  (D.B_spec a C.aU c C.cU).mpr (by
    rw [C.V_comm a C.aV c C.cV]
    group)

theorem hatV_eq (x : D.V) (hx : x ∈ D.hat V) :
    x = 0 ∨ x = D.π a ∨ x = D.π c ∨ x = D.π a + D.π c := by
  classical
  have hu := C.pi_a_ne
  have hw := C.pi_c_ne
  have huw := C.pi_a_ne_c
  set S : Finset D.V := {0, D.π a, D.π c, D.π a + D.π c} with hS
  have hsub : (S : Set D.V) ⊆ (D.hat V : Set D.V) := by
    intro y hy
    simp only [hS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact (D.hat V).zero_mem
    · exact C.pi_a_mem
    · exact C.pi_c_mem
    · exact (D.hat V).add_mem C.pi_a_mem C.pi_c_mem
  have hcard : S.card = 4 := by
    have h1 : D.π a + D.π c ≠ 0 := fun h => huw (by
      have := congrArg (· + D.π c) h
      simpa [add_assoc, ZModModule.add_self] using this)
    have h2 : D.π a + D.π c ≠ D.π a := fun h => hw (by
      have := congrArg (D.π a + ·) h
      simpa [← add_assoc, ZModModule.add_self] using this)
    have h3 : D.π a + D.π c ≠ D.π c := fun h => hu (by
      have := congrArg (· + D.π c) h
      simpa [add_assoc, ZModModule.add_self] using this)
    rw [hS, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair h3.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨huw, h2.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hu.symm, hw.symm, h1.symm⟩
  have heq : (S : Set D.V) = (D.hat V : Set D.V) := by
    apply Set.eq_of_subset_of_ncard_le hsub
    rw [Set.ncard_coe_finset, hcard, ← C.card_hatV, ← Nat.card_coe_set_eq]
    rfl
  have hx' : x ∈ (S : Set D.V) := by rw [heq]; exact hx
  simpa [hS] using hx'

theorem card_V : Nat.card D.V = 16 := by
  have : Module.Finite (ZMod 2) D.V := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), C.d4, Nat.card_zmod]
  norm_num

theorem imgT_le : D.img T ≤ D.img (l32nH T V) := img_mono D C.TH

theorem imgT_stab : D.img T ≤ Sp4Cert.stabW (D.hat V) := by
  intro γ hγ
  refine Sp4Cert.mem_stabW.mpr fun w hw => ?_
  obtain ⟨x, hxT, hxN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
  obtain ⟨b, hbV, hbU, rfl⟩ := (L128A.HatU.mem_hat D).mp hw
  rw [D.ρ_π ⟨x, hxN⟩ b hbU]
  have hxb : x * b * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (C.TV hxT) b).mp hbV
  exact L128A.HatU.π_mem_hat D hxb (C.V_U hxb)

theorem isPGroup_imgT : IsPGroup 2 ↥(D.img T) :=
  isPGroup_img D C.T2 (C.TH.trans (L14332.l32nH_le_normalizer_fsuU T V))

theorem card_img_eq : Nat.card ↥(D.img (l32nH T V)) =
    Nat.card ↥(D.img T) * (D.img T).relIndex (D.img (l32nH T V)) := by
  have h1 := ((D.img T).subgroupOf (D.img (l32nH T V))).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe C.imgT_le).toEquiv] at h1
  exact h1.symm

theorem gcd_dvd : Nat.gcd (Nat.card ↥(D.img (l32nH T V))) 16 ∣ Nat.card ↥(D.img T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := L14332.finite_linearEquiv D
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp C.isPGroup_imgT
  rw [C.card_img_eq, hk]
  have hcop : Nat.Coprime ((D.img T).relIndex (D.img (l32nH T V))) 16 := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
    exact (Nat.Coprime.pow_left 4 (Nat.coprime_two_left.mpr C.Todd)).symm
  rw [Nat.Coprime.gcd_mul_right_cancel _ hcop]
  exact Nat.gcd_dvd_left _ _

theorem hT : Nat.gcd (Nat.card ↥(D.img (l32nH T V))) 16 ∣
    Nat.card ↥(D.img (l32nH T V) ⊓ Sp4Cert.stabW (D.hat V)) :=
  C.gcd_dvd.trans (Subgroup.card_dvd_of_le (le_inf C.imgT_le C.imgT_stab))

theorem exists_y : ∃ y ∈ D.img (lOne L (fsuV1 T V)), y ∈ D.img (l32nH T V) ∧
    y ∈ Sp4Cert.stabW (D.hat V) ∧ y ^ 3 = 1 ∧ y (D.π a) = D.π c := by
  obtain ⟨l, hlL, hl3, hlH, hla⟩ := C.rot
  have hlN : l ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    L14332.l32nH_le_normalizer_fsuU T V hlH
  have hodd : Odd (orderOf l) :=
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hl3)
  have hl1 : l ∈ lOne L (fsuV1 T V) := mem_oTwoUpper_of_odd ⟨hlL, hlH⟩ hodd
  refine ⟨D.ρ ⟨l, hlN⟩, L128A.HatU.rho_mem_img D hl1 hlN, L128A.HatU.rho_mem_img D hlH hlN,
    ?_, ?_, ?_⟩
  · refine Sp4Cert.mem_stabW.mpr fun w hw => ?_
    obtain ⟨b, hbV, hbU, rfl⟩ := (L128A.HatU.mem_hat D).mp hw
    rw [D.ρ_π ⟨l, hlN⟩ b hbU]
    have hlb : l * b * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (C.LV hlL) b).mp hbV
    exact L128A.HatU.π_mem_hat D hlb (C.V_U hlb)
  · have h1 : (⟨l, hlN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hl3)
    rw [← map_pow, h1, map_one]
  · rw [D.ρ_π ⟨l, hlN⟩ a C.aU]
    show D.π (l * a * l⁻¹) = D.π c
    rw [hla]

theorem h3 : ∃ y ∈ D.img (l32nH T V), y ∈ Sp4Cert.stabW (D.hat V) ∧ y ≠ 1 ∧ y ^ 3 = 1 ∧
    ∃ x ∈ D.hat V, y x ≠ x := by
  obtain ⟨y, -, hyH, hyS, hy3, hya⟩ := C.exists_y
  have hmove : y (D.π a) ≠ D.π a := fun h => C.pi_a_ne_c (hya.symm.trans h).symm
  exact ⟨y, hyH, hyS, fun h1 => hmove (by subst h1; rfl), hy3, D.π a, C.pi_a_mem, hmove⟩

theorem hne : ¬ D.img (l32nH T V) ≤ Sp4Cert.stabW (D.hat V) := by
  intro hmaps
  have hHN := L14332.l32nH_le_normalizer_fsuU T V
  have hU : ∀ u ∈ fsuU T V, D.π u ∈ D.hat V := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, hk, v, hv, rfl⟩ := hy
      rw [← D.ρ_π ⟨k, hHN hk⟩ v (C.V_U hv)]
      exact Sp4Cert.mem_stabW.mp (hmaps (L128A.HatU.rho_mem_img D hk (hHN hk))) _
        (L128A.HatU.π_mem_hat D hv (C.V_U hv))
    | one => rw [L128A.HatU.π_one]; exact Submodule.zero_mem _
    | mul y y' hy hy' ih ih' =>
      rw [D.π_mul y hy y' hy']
      exact Submodule.add_mem _ ih ih'
    | inv y hy ih =>
      rw [L128A.HatU.π_inv D hy]
      exact Submodule.neg_mem _ ih
  have htop : D.hat V = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨u, hu, rfl⟩ := D.π_surj v
    exact hU u hu
  have h2 : Nat.card ↥(⊤ : Submodule (ZMod 2) D.V) = Nat.card D.V :=
    Nat.card_congr Submodule.topEquiv.toEquiv
  have h4 := C.card_hatV
  rw [htop, h2, C.card_V] at h4
  omega

theorem X_le : D.img (CFSG.conjugate (l32nW T V V₂) g) ≤ D.img (l32nH T V) :=
  img_mono D C.Wg_le

theorem exists_t : ∃ t ∈ D.img (CFSG.conjugate (l32nW T V V₂) g),
    t (D.π c) = D.π c + D.π a ∧ ∀ w ∈ D.hat V, t w ∈ D.hat V := by
  have h01 : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by decide
  have haE : D.π a ∈ D.hat (l32nE T V V₂ g) := by rw [← C.hatV]; exact C.pi_a_mem
  have hcE : D.π c ∈ D.hat (l32nE T V V₂ g) := by rw [← C.hatV]; exact C.pi_c_mem
  have hnot : (⟨D.π c, hcE⟩ : ↥(D.hat (l32nE T V V₂ g))) ∉
      (ZMod 2) ∙ (⟨D.π a, haE⟩ : ↥(D.hat (l32nE T V V₂ g))) := by
    intro hmem
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    have hr' : r • D.π a = D.π c := congrArg Subtype.val hr
    rcases h01 r with rfl | rfl
    · exact C.pi_c_ne (by rw [← hr', zero_smul])
    · exact C.pi_a_ne_c (by rw [← hr', one_smul])
  obtain ⟨f, hf, hpk⟩ := Submodule.exists_le_ker_of_notMem hnot
  have hfa : f ⟨D.π a, C.g101.mem_W⟩ = 0 :=
    LinearMap.mem_ker.mp (hpk (Submodule.mem_span_singleton_self _))
  have hfc : f ⟨D.π c, hcE⟩ = 1 := by
    rcases h01 (f ⟨D.π c, hcE⟩) with h | h
    · exact absurd h hf
    · exact h
  obtain ⟨t, htX, ht⟩ := C.g101.transvection_full f hfa
  refine ⟨t, htX, ?_, fun w hw => ?_⟩
  · have h1 := ht ⟨D.π c, hcE⟩
    rw [hfc, one_smul] at h1
    exact h1
  · have hwE : w ∈ D.hat (l32nE T V V₂ g) := by rw [← C.hatV]; exact hw
    have h1 : t w = w + f ⟨w, hwE⟩ • D.π a := ht ⟨w, hwE⟩
    rw [h1]
    exact (D.hat V).add_mem hw ((D.hat V).smul_mem _ C.pi_a_mem)

theorem h2 : ∃ t ∈ D.img (l32nH T V), t ∈ Sp4Cert.stabW (D.hat V) ∧ t ≠ 1 ∧ t ^ 2 = 1 ∧
    ∃ x ∈ D.hat V, t x ≠ x := by
  obtain ⟨t, htX, htc, htV⟩ := C.exists_t
  have hmove : t (D.π c) ≠ D.π c := by
    rw [htc]
    intro h
    exact C.pi_a_ne (by simpa using h)
  refine ⟨t, C.X_le htX, Sp4Cert.mem_stabW.mpr htV, fun h1 => hmove (by subst h1; rfl), ?_,
    D.π c, C.pi_c_mem, hmove⟩
  rw [pow_two]
  exact C.g101.X_sq t htX

theorem zU_le_fix : D.img (CFSG.conjugate (centerOf (fsuU T V)) g) ≤
    D.img (l32nH T V) ⊓ Sp4Cert.fixW (D.hat V) :=
  le_inf (img_mono D C.zUg_le) fun x hx => Sp4Cert.mem_fixingSubgroup_iff'.mpr (C.zU_fix x hx)

omit [Finite G] C in
theorem zU_comm_X {z x : D.V ≃ₗ[ZMod 2] D.V}
    (hz : z ∈ D.img (CFSG.conjugate (centerOf (fsuU T V)) g))
    (hx : x ∈ D.img (CFSG.conjugate (l32nW T V V₂) g)) : z * x = x * z := by
  obtain ⟨ζ, hζ, hζN, rfl⟩ := (L128A.HatU.mem_img D).mp hz
  obtain ⟨w, hw, hwN, rfl⟩ := (L128A.HatU.mem_img D).mp hx
  obtain ⟨ζ₀, hζ₀, rfl⟩ := hζ
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  have hc : ζ₀ * w₀ = w₀ * ζ₀ :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hζ₀).2 w₀
      (Subgroup.mem_inf.mp hw₀).1).symm
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show (MulAut.conj g⁻¹) ζ₀ * (MulAut.conj g⁻¹) w₀ = (MulAut.conj g⁻¹) w₀ * (MulAut.conj g⁻¹) ζ₀
  rw [← map_mul, ← map_mul, hc]

end Ctx

end L14323

end CFSG.Quasithin.H13
