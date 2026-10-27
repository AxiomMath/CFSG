module

public import CFSG.Quasithin.Vol2.Ch10SecBMax
public import CFSG.Quasithin.Vol2.Ch10SecBL32Xi
public import CFSG.Quasithin.Vol2.Ch1Xi
public import CFSG.Quasithin.Vol2.Ch10SecBL32O2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

structure ParData (A K E : Subgroup L32.Γ) : Prop where
  uA : L32.U3 ≤ A
  o2 : oTwoUpper (A.prod A) = K.prod K
  EK : E ≤ K
  KA : K ≤ A
  normE : ∀ g ∈ A, ∀ e ∈ E, g * e * g⁻¹ ∈ E
  cube : ∀ k ∈ K, k * k * k ∈ E
  comm : ∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ E
  two : ∀ k ∈ K, ∀ n : ℕ, k ^ 2 ^ n = 1 → k ∈ E
  cardK : Nat.card K = 12
  cardE : Nat.card E = 4
  irred : ∀ {B : Subgroup (L32.Γ × L32.Γ)} {c : L32.Γ}, L32.IsU c → E.prod E ≤ B →
    B ≤ K.prod K → (∀ u ∈ L32.U3.prod L32.U3, ∀ p ∈ B, u * p * u⁻¹ ∈ B) →
    (∀ p ∈ B, (c * p.2 * c⁻¹, p.1) ∈ B) → B = E.prod E ∨ B = K.prod K
  sq : ∀ u ∈ L32.U3, ∀ k ∈ K, u * u * k * (u * u)⁻¹ * k⁻¹ ∈ E
  noncomm : ∃ d ∈ L32.U3, ∃ k ∈ K, d * k * d⁻¹ * k⁻¹ ∉ E

theorem parData_a : ParData L32.Pa L32.Ka L32.Ea where
  uA := L32.u3_le_pa
  o2 := L32.oTwoUpper_pa_prod
  EK := fun k hk => (L32.ea_le k hk).1
  KA := fun _ hk => hk.1
  normE := fun g hg e he => L32.ea_normal g e hg he
  cube := fun k hk => L32.ka_cube k hk
  comm := fun a ha b hb => L32.ka_comm a b ha hb
  two := fun _ hk _ hn => L32.isEa_of_two_pow hk hn
  cardK := L32.card_Ka'
  cardE := L32.card_Ea'
  irred := fun hc hEB hBK hU hσ => L32.ka_prod_irred hc hEB hBK hU hσ
  sq := fun u hu k hk => L32.ka_sq u k hu hk
  noncomm := by
    obtain ⟨d, hd, k, hk, h⟩ := L32.ka_noncomm
    exact ⟨d, hd, k, hk, h⟩

theorem parData_b : ParData L32.Pb L32.Kb L32.Eb where
  uA := L32.u3_le_pb
  o2 := L32.oTwoUpper_pb_prod
  EK := fun k hk => (L32.eb_le k hk).1
  KA := fun _ hk => hk.1
  normE := fun g hg e he => L32.eb_normal g e hg he
  cube := fun k hk => L32.kb_cube k hk
  comm := fun a ha b hb => L32.kb_comm a b ha hb
  two := fun _ hk _ hn => L32.isEb_of_two_pow hk hn
  cardK := L32.card_Kb'
  cardE := L32.card_Eb'
  irred := fun hc hEB hBK hU hσ => L32.kb_prod_irred hc hEB hBK hU hσ
  sq := fun u hu k hk => L32.kb_sq u k hu hk
  noncomm := by
    obtain ⟨d, hd, k, hk, h⟩ := L32.kb_noncomm
    exact ⟨d, hd, k, hk, h⟩

section General

variable {G : Type*} [Group G]

theorem oTwoUpper_sup_eq {Y R : Subgroup G} (hR : IsPGroup 2 R)
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) : oTwoUpper (Y ⊔ R) = oTwoUpper Y := by
  refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => ?_) (oTwoUpper_mono le_sup_left)
  obtain ⟨hxYR, hodd⟩ := hx
  have hx' : x ∈ ((Y ⊔ R : Subgroup G) : Set G) := hxYR
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Y R hRY] at hx'
  obtain ⟨y, hy, r, hr, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨j, hj⟩ := hR ⟨r, hr⟩
  have hj' : r ^ 2 ^ j = 1 := congrArg Subtype.val hj
  obtain ⟨y', hy', hpow⟩ := A4.exists_pow_mul_eq hy (hRY hr) (2 ^ j)
  rw [hj', mul_one] at hpow
  have hcop : Nat.Coprime (2 ^ j) (orderOf (y * r)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have hmem := A4.mem_zpowers_pow_of_coprime hcop
  rw [hpow] at hmem
  exact mem_oTwoUpper_of_odd ((Subgroup.zpowers_le.mpr hy') hmem) hodd

theorem oTwoUpper_oTwoUpper' (X : Subgroup G) : oTwoUpper (oTwoUpper X) = oTwoUpper X :=
  le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun _ hx =>
    mem_oTwoUpper_of_odd (Subgroup.subset_closure hx) hx.2)

end General

variable {G : Type} [Group G] [Finite G]

structure MaxCtx (T L I : Subgroup G) (t : G) (Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ)
    (c : L32.Γ) : Prop where
  h37 : Vol2Native.A37ForSQTKCat
  h38 : Vol2Native.A38ForSQTKCat
  hyp : Hyp10 G T L I
  ht : t ∈ T
  htn : t ∉ Subgroup.normalizer (L : Set G)
  hC : L0Coord T L t Ψ c

abbrev XOf (T L : Subgroup G) (Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ) (A : Subgroup L32.Γ) :
    Subgroup G :=
  oTwoUpper (preIn Ψ (A.prod A) ⊔ T)

variable {T L I : Subgroup G} {t : G} {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ}
  {A K E : Subgroup L32.Γ}

theorem XOf_eq (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) :
    XOf T L Ψ A = oTwoUpper (preIn Ψ (A.prod A)) :=
  oTwoUpper_sup_eq h.hyp.fsu.sylow.1 (le_normalizer_preIn h.h37 h.h38 h.hyp h.ht h.htn h.hC hD.uA)

theorem XOf_le_fsuL0 (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) :
    XOf T L Ψ A ≤ fsuL0 T L := by
  rw [XOf_eq h hD]
  exact (oTwoUpper_le _).trans (preIn_le Ψ _)

theorem imgIn_XOf (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) :
    imgIn Ψ (XOf T L Ψ A) = K.prod K := by
  rw [XOf_eq h hD, imgIn_oTwoUpper Ψ (preIn_le Ψ _), imgIn_preIn h.hC.surj, hD.o2]

theorem mem_prod_of_mem_XOf (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) {x : G}
    (hx : x ∈ XOf T L Ψ A) : Ψ ⟨x, XOf_le_fsuL0 h hD hx⟩ ∈ K.prod K := by
  rw [← imgIn_XOf h hD]
  exact mem_imgIn.mpr ⟨x, _, hx, rfl⟩

theorem isPGroup_preIn (hC : L0Coord T L t Ψ c) {B : Subgroup (L32.Γ × L32.Γ)}
    (hB : IsPGroup 2 B) : IsPGroup 2 (preIn Ψ B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨y, hy⟩
  obtain ⟨hyL0, hyB⟩ := mem_preIn.mp hy
  obtain ⟨j, hj⟩ := hB ⟨_, hyB⟩
  have hj' : (Ψ ⟨y, hyL0⟩) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have h1 : Ψ (⟨y, hyL0⟩ ^ 2 ^ j) = 1 := by rw [map_pow, hj']
  have h2 : y ^ 2 ^ j ∈ pCoreOf 2 (fsuL0 T L) := (hC.ker _).mp h1
  obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (fsuL0 T L) ⟨_, h2⟩
  have hm' : (y ^ 2 ^ j) ^ 2 ^ m = 1 := congrArg Subtype.val hm
  refine ⟨j + m, Subtype.ext ?_⟩
  show y ^ 2 ^ (j + m) = 1
  rw [pow_add, pow_mul, hm']

theorem card_prod_self (K : Subgroup L32.Γ) : Nat.card (K.prod K) = Nat.card K * Nat.card K := by
  rw [Nat.card_congr (Subgroup.prodEquiv K K).toEquiv, Nat.card_prod]

theorem isPGroup_prod_E (hD : ParData A K E) : IsPGroup 2 (E.prod E) :=
  IsPGroup.of_card (n := 4) (by rw [card_prod_self, hD.cardE]; norm_num)

theorem conj_mem_inf_preIn (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) {x y : G}
    (hx : x ∈ XOf T L Ψ A) (hy : y ∈ XOf T L Ψ A ⊓ preIn Ψ (E.prod E)) :
    x * y * x⁻¹ ∈ XOf T L Ψ A ⊓ preIn Ψ (E.prod E) := by
  have hXL0 := XOf_le_fsuL0 h hD
  obtain ⟨hyX, hyE⟩ := hy
  obtain ⟨hyL0, hyE'⟩ := mem_preIn.mp hyE
  have hm : x * y * x⁻¹ ∈ XOf T L Ψ A := (XOf T L Ψ A).mul_mem
    ((XOf T L Ψ A).mul_mem hx hyX) ((XOf T L Ψ A).inv_mem hx)
  refine ⟨hm, mem_preIn.mpr ⟨hXL0 hm, ?_⟩⟩
  have hxK := mem_prod_of_mem_XOf h hD hx
  rw [show (⟨x * y * x⁻¹, hXL0 hm⟩ : ↥(fsuL0 T L)) =
    ⟨x, hXL0 hx⟩ * ⟨y, hyL0⟩ * ⟨x, hXL0 hx⟩⁻¹ from rfl, map_mul, map_mul, map_inv]
  exact ⟨hD.normE _ (hD.KA hxK.1) _ hyE'.1, hD.normE _ (hD.KA hxK.2) _ hyE'.2⟩

theorem pCoreOf_XOf (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) :
    pCoreOf 2 (XOf T L Ψ A) = XOf T L Ψ A ⊓ preIn Ψ (E.prod E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXL0 := XOf_le_fsuL0 h hD
  apply le_antisymm
  · intro y hy
    have hyX : y ∈ XOf T L Ψ A := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hy
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (XOf T L Ψ A) ⟨y, hy⟩
    have hj' : y ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hΨ := mem_prod_of_mem_XOf h hD hyX
    have hpow : (Ψ ⟨y, hXL0 hyX⟩) ^ 2 ^ j = 1 := by
      rw [← map_pow]
      have : (⟨y, hXL0 hyX⟩ : ↥(fsuL0 T L)) ^ 2 ^ j = 1 := Subtype.ext hj'
      rw [this, map_one]
    refine ⟨hyX, mem_preIn.mpr ⟨hXL0 hyX, ?_, ?_⟩⟩
    · exact hD.two _ hΨ.1 j (by have := congrArg Prod.fst hpow; simpa using this)
    · exact hD.two _ hΨ.2 j (by have := congrArg Prod.snd hpow; simpa using this)
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (fun x hx => ?_)
      ((isPGroup_preIn h.hC (isPGroup_prod_E hD)).to_le inf_le_right)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_inf_preIn h hD hx hy, fun hy => ?_⟩
    have := conj_mem_inf_preIn h hD ((XOf T L Ψ A).inv_mem hx) hy
    simpa [mul_assoc] using this

theorem pow_three_mem (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) {x : G}
    (hx : x ∈ XOf T L Ψ A) : x ^ 3 ∈ pCoreOf 2 (XOf T L Ψ A) := by
  have hXL0 := XOf_le_fsuL0 h hD
  rw [pCoreOf_XOf h hD]
  have hm : x ^ 3 ∈ XOf T L Ψ A := (XOf T L Ψ A).pow_mem hx 3
  refine ⟨hm, mem_preIn.mpr ⟨hXL0 hm, ?_⟩⟩
  have hxK := mem_prod_of_mem_XOf h hD hx
  rw [show (⟨x ^ 3, hXL0 hm⟩ : ↥(fsuL0 T L)) = ⟨x, hXL0 hx⟩ ^ 3 from rfl, map_pow]
  refine ⟨?_, ?_⟩
  · show (Ψ ⟨x, hXL0 hx⟩).1 ^ 3 ∈ E
    rw [pow_three, ← mul_assoc]
    exact hD.cube _ hxK.1
  · show (Ψ ⟨x, hXL0 hx⟩).2 ^ 3 ∈ E
    rw [pow_three, ← mul_assoc]
    exact hD.cube _ hxK.2

theorem commutator_le_pCoreOf (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) :
    ⁅XOf T L Ψ A, XOf T L Ψ A⁆ ≤ pCoreOf 2 (XOf T L Ψ A) := by
  have hXL0 := XOf_le_fsuL0 h hD
  rw [pCoreOf_XOf h hD, Subgroup.commutator_le]
  intro a ha b hb
  have hm : ⁅a, b⁆ ∈ XOf T L Ψ A := by
    rw [commutatorElement_def]
    exact (XOf T L Ψ A).mul_mem ((XOf T L Ψ A).mul_mem ((XOf T L Ψ A).mul_mem ha hb)
      ((XOf T L Ψ A).inv_mem ha)) ((XOf T L Ψ A).inv_mem hb)
  refine ⟨hm, mem_preIn.mpr ⟨hXL0 hm, ?_⟩⟩
  have haK := mem_prod_of_mem_XOf h hD ha
  have hbK := mem_prod_of_mem_XOf h hD hb
  rw [show (⟨⁅a, b⁆, hXL0 hm⟩ : ↥(fsuL0 T L)) = ⟨a, hXL0 ha⟩ * ⟨b, hXL0 hb⟩ *
    ⟨a, hXL0 ha⟩⁻¹ * ⟨b, hXL0 hb⟩⁻¹ from rfl, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact ⟨hD.comm _ haK.1 _ hbK.1, hD.comm _ haK.2 _ hbK.2⟩

omit [Finite G] in
theorem eq_inf_preIn_imgIn {X Y : Subgroup G} (hYX : Y ≤ X) (hXL0 : X ≤ fsuL0 T L)
    (hker : ∀ x ∈ X, ∀ hx : x ∈ fsuL0 T L, Ψ ⟨x, hx⟩ = 1 → x ∈ Y) :
    Y = X ⊓ preIn Ψ (imgIn Ψ Y) := by
  refine le_antisymm (fun y hy => ⟨hYX hy, mem_preIn.mpr ⟨hXL0 (hYX hy),
    mem_imgIn.mpr ⟨y, _, hy, rfl⟩⟩⟩) fun x hx => ?_
  obtain ⟨hxX, hxB⟩ := hx
  obtain ⟨hxL0, hq⟩ := mem_preIn.mp hxB
  obtain ⟨y, hyL0, hyY, hyx⟩ := mem_imgIn.mp hq
  have hm : y⁻¹ * x ∈ X := X.mul_mem (X.inv_mem (hYX hyY)) hxX
  have h1 : Ψ ⟨y⁻¹ * x, hXL0 hm⟩ = 1 := by
    rw [show (⟨y⁻¹ * x, hXL0 hm⟩ : ↥(fsuL0 T L)) = ⟨y, hyL0⟩⁻¹ * ⟨x, hxL0⟩ from rfl, map_mul,
      map_inv, hyx, inv_mul_cancel]
  have := Y.mul_mem hyY (hker _ hm _ h1)
  simpa using this

theorem relIndex_XOf (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) :
    (pCoreOf 2 (XOf T L Ψ A)).relIndex (XOf T L Ψ A) = 9 := by
  have hXL0 := XOf_le_fsuL0 h hD
  set f : ↥(XOf T L Ψ A) →* L32.Γ × L32.Γ := Ψ.comp (Subgroup.inclusion hXL0) with hf
  have h1 : (preIn Ψ (E.prod E)).subgroupOf (XOf T L Ψ A) = (E.prod E).comap f := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, mem_preIn]
    exact ⟨fun ⟨_, hx⟩ => hx, fun hx => ⟨hXL0 x.2, hx⟩⟩
  have h2 : f.range = K.prod K := by
    rw [← imgIn_XOf h hD]
    ext q
    rw [MonoidHom.mem_range, mem_imgIn]
    exact ⟨fun ⟨x, hx⟩ => ⟨x, hXL0 x.2, x.2, hx⟩, fun ⟨x, _, hxX, hx⟩ => ⟨⟨x, hxX⟩, hx⟩⟩
  have h3 : (E.prod E).relIndex (K.prod K) * Nat.card (E.prod E) = 144 := by
    have := Subgroup.relIndex_mul_card (H := E.prod E) (K := K.prod K)
    rwa [inf_eq_left.mpr (Subgroup.prod_mono hD.EK hD.EK), card_prod_self K, hD.cardK] at this
  rw [card_prod_self, hD.cardE] at h3
  rw [pCoreOf_XOf h hD, Subgroup.inf_relIndex_left, Subgroup.relIndex, h1, Subgroup.index_comap,
    h2]
  omega

theorem irred_XOf (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) {Y : Subgroup G}
    (h1 : pCoreOf 2 (XOf T L Ψ A) ≤ Y) (h2 : Y ≤ XOf T L Ψ A)
    (h3 : T ≤ Subgroup.normalizer (Y : Set G)) :
    Y = pCoreOf 2 (XOf T L Ψ A) ∨ Y = XOf T L Ψ A := by
  have hXL0 := XOf_le_fsuL0 h hD
  have hC := h.hC
  have hEB : E.prod E ≤ imgIn Ψ Y := by
    intro p hp
    have hpK : p ∈ imgIn Ψ (XOf T L Ψ A) := by
      rw [imgIn_XOf h hD]; exact Subgroup.prod_mono hD.EK hD.EK hp
    obtain ⟨x, hxL0, hxX, rfl⟩ := mem_imgIn.mp hpK
    have hxO : x ∈ pCoreOf 2 (XOf T L Ψ A) := by
      rw [pCoreOf_XOf h hD]; exact ⟨hxX, mem_preIn.mpr ⟨hxL0, hp⟩⟩
    exact mem_imgIn.mpr ⟨x, hxL0, h1 hxO, rfl⟩
  have hBK : imgIn Ψ Y ≤ K.prod K := by rw [← imgIn_XOf h hD]; exact imgIn_mono Ψ h2
  have hU : ∀ u ∈ L32.U3.prod L32.U3, ∀ p ∈ imgIn Ψ Y, u * p * u⁻¹ ∈ imgIn Ψ Y := by
    intro u hu p hp
    rw [← hC.T0] at hu
    obtain ⟨⟨s, hsL0⟩, hsT0, rfl⟩ := hu
    obtain ⟨y, hyL0, hyY, rfl⟩ := mem_imgIn.mp hp
    have hsT : s ∈ T := (Subgroup.mem_subgroupOf.mp hsT0).1
    have hm : s * y * s⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (h3 hsT) y).mp hyY
    refine mem_imgIn.mpr ⟨s * y * s⁻¹, hXL0 (h2 hm), hm, ?_⟩
    rw [show (⟨s * y * s⁻¹, hXL0 (h2 hm)⟩ : ↥(fsuL0 T L)) =
      ⟨s, hsL0⟩ * ⟨y, hyL0⟩ * ⟨s, hsL0⟩⁻¹ from rfl, map_mul, map_mul, map_inv]
  have hσ : ∀ p ∈ imgIn Ψ Y, (c * p.2 * c⁻¹, p.1) ∈ imgIn Ψ Y := by
    intro p hp
    obtain ⟨y, hyL0, hyY, rfl⟩ := mem_imgIn.mp hp
    have hm : t⁻¹ * y * t ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (h3 (T.inv_mem h.ht)) y).mp hyY
      simpa using this
    exact mem_imgIn.mpr ⟨_, hXL0 (h2 hm), hm, hC.swap ⟨y, hyL0⟩ (hXL0 (h2 hm))⟩
  have hker : ∀ x ∈ XOf T L Ψ A, ∀ hx : x ∈ fsuL0 T L, Ψ ⟨x, hx⟩ = 1 → x ∈ Y := by
    intro x hxX hx h1'
    refine h1 ?_
    rw [pCoreOf_XOf h hD]
    exact ⟨hxX, mem_preIn.mpr ⟨hx, by rw [h1']; exact (E.prod E).one_mem⟩⟩
  have hY := eq_inf_preIn_imgIn h2 hXL0 hker
  rcases hD.irred hC.hc hEB hBK hU hσ with hB | hB
  · left
    rw [hY, hB, pCoreOf_XOf h hD]
  · right
    rw [hY, hB]
    exact inf_eq_left.mpr fun x hx => mem_preIn.mpr ⟨hXL0 hx, mem_prod_of_mem_XOf h hD hx⟩

theorem isXi_XOf (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) : IsXi T (XOf T L Ψ A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXL0 := XOf_le_fsuL0 h hD
  have hT := h.hyp.fsu.sylow
  refine ⟨(oTwoUpper_oTwoUpper' _).symm, le_sup_right.trans (le_normalizer_oTwoUpper _),
    fun hbot => ?_, 3, Nat.prime_three, by norm_num, fun x hx => pow_three_mem h hD hx,
    Or.inl (by rw [relIndex_XOf h hD]; norm_num), fun Y h1 h2 h3 => ?_⟩
  · apply SecA.pCoreOf_fsuM_ne_bot h.hyp.fsu.faithful
    refine le_bot_iff.mp (hbot ▸ ?_)
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((SecA.pCoreOf_le_of_sylow hT (SecA.le_fsuM T L)).trans le_sup_right) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact (sup_le (hXL0.trans (SecA.fsuL0_le_fsuM T L)) (SecA.le_fsuM T L)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  · have hc : ⁅XOf T L Ψ A, XOf T L Ψ A⁆ ⊔ pCoreOf 2 (XOf T L Ψ A) =
        pCoreOf 2 (XOf T L Ψ A) := sup_eq_right.mpr (commutator_le_pCoreOf h hD)
    rw [hc] at h1 ⊢
    exact irred_XOf h hD h1 h2 h3

end CFSG.Quasithin.Vol2.Ch10.SecB
