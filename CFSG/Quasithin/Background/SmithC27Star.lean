module

public import CFSG.Quasithin.Background.AutOnCard
public import CFSG.Quasithin.Background.C124B2102
public import CFSG.Quasithin.Background.C2Defs

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

section General

variable {V : Subgroup G}

omit [Finite G] in
theorem mem_autOn_iff' {Y : Subgroup G} {φ : MulAut ↥V} :
    φ ∈ autOn Y V ↔
      ∃ n : ↥(Subgroup.normalizer (V : Set G)), (n : G) ∈ Y ∧ conjAct V n = φ := by
  unfold autOn
  rw [Subgroup.mem_map]
  simp only [Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem conjAct_eq_one_iff' (n : ↥(Subgroup.normalizer (V : Set G))) :
    conjAct V n = 1 ↔ (n : G) ∈ Subgroup.centralizer (V : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff n

omit [Finite G] in
theorem autOn_mono' {Y Y' : Subgroup G} (h : Y ≤ Y') : autOn Y V ≤ autOn Y' V :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono _ h)

omit [Finite G] in
theorem isPGroup_autOn {Y : Subgroup G} (hY : IsPGroup 2 Y) : IsPGroup 2 (autOn Y V) :=
  CFSG.Quasithin.AutOn.isPGroup_autOn hY

omit [Finite G] in
theorem card_eq_card_autOn_mul {Y : Subgroup G} (hY : Y ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card Y = Nat.card (autOn Y V) * Nat.card ↥(Y ⊓ Subgroup.centralizer (V : Set G)) :=
  (CFSG.Quasithin.AutOn.card_autOn_mul hY).symm

omit [Finite G] in
theorem card_eq_index_mul {A B : Subgroup G} (h : A ≤ B) :
    Nat.card B = (A.subgroupOf B).index * Nat.card A := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv, Subgroup.index_mul_card]

omit [Finite G] in
theorem card_eq_index_mul' [Finite V] {A B : Subgroup (MulAut ↥V)} (h : A ≤ B) :
    Nat.card B = (A.subgroupOf B).index * Nat.card A := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv, Subgroup.index_mul_card]

theorem isSylowTwoOf_iff_autOn {S Y : Subgroup G} (hY : Y ≤ Subgroup.normalizer (V : Set G))
    (hSY : S ≤ Y) (hS : IsPGroup 2 S)
    (hC : IsSylowTwoOf (S ⊓ Subgroup.centralizer (V : Set G))
      (Y ⊓ Subgroup.centralizer (V : Set G))) :
    IsSylowTwoOf S Y ↔ IsSylowTwoOf (autOn S V) (autOn Y V) := by
  have h1 := card_eq_card_autOn_mul hY
  have h2 := card_eq_card_autOn_mul (hSY.trans hY)
  have hSYs : autOn S V ≤ autOn Y V := autOn_mono' hSY
  have hCC : S ⊓ Subgroup.centralizer (V : Set G) ≤ Y ⊓ Subgroup.centralizer (V : Set G) :=
    inf_le_inf_right _ hSY
  have i1 := card_eq_index_mul hSY
  have i2 := card_eq_index_mul' hSYs
  have i3 := card_eq_index_mul hCC
  set a := (S.subgroupOf Y).index
  set b := ((autOn S V).subgroupOf (autOn Y V)).index
  set c := ((S ⊓ Subgroup.centralizer (V : Set G)).subgroupOf
    (Y ⊓ Subgroup.centralizer (V : Set G))).index
  have hpos1 : 0 < Nat.card ↥(autOn S V) := Nat.card_pos
  have hpos2 : 0 < Nat.card ↥(S ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
  have key : a = b * c := by
    have e : a * (Nat.card ↥(autOn S V) * Nat.card ↥(S ⊓ Subgroup.centralizer (V : Set G))) =
        (b * c) * (Nat.card ↥(autOn S V) * Nat.card ↥(S ⊓ Subgroup.centralizer (V : Set G))) := by
      rw [← h2, ← i1, h1, i2, i3, h2]
      ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpos1 hpos2) e
  have hc : ¬ 2 ∣ c := hC.2.2
  constructor
  · rintro ⟨-, -, ha⟩
    refine ⟨hSYs, isPGroup_autOn hS, fun hb => ha ?_⟩
    show 2 ∣ a
    rw [key]
    exact Dvd.dvd.mul_right hb c
  · rintro ⟨-, -, hb⟩
    refine ⟨hSY, hS, fun ha => ?_⟩
    have ha' : 2 ∣ a := ha
    rw [key] at ha'
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 ha' with h | h
    · exact hb h
    · exact hc h

omit [Finite G] in
theorem oTwoZIn_le' (L : Subgroup G) : oTwoZIn L ≤ L := by
  unfold oTwoZIn preimageModTwoCore
  exact Subgroup.map_subtype_le _

omit [Finite G] in
theorem pCore_le_oTwoZIn' (L : Subgroup G) : pCoreOf 2 L ≤ oTwoZIn L := by
  rw [C124.pCoreOf_eq_map_pCore]
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y, Subgroup.mem_comap.2 ?_, rfl⟩
  have : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) y = 1 := (QuotientGroup.eq_one_iff y).2 hy
  rw [this]
  exact Subgroup.one_mem _

omit [Finite G] in
theorem oTwoZIn_eq_of_center_eq_bot {L : Subgroup G}
    (hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥) : oTwoZIn L = pCoreOf 2 L := by
  unfold oTwoZIn preimageModTwoCore
  rw [hZ, MonoidHom.comap_bot, QuotientGroup.ker_mk', ← C124.pCoreOf_eq_map_pCore]

end General

section Basic

omit [Finite G]

structure StarHyp (R K V : Subgroup G) : Prop where
  norm : R ≤ Subgroup.normalizer (K : Set G)
  pgroup : IsPGroup 2 R
  quasi : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)
  red : IsTwoReducedIn (K ⊔ R) V
  cent : (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K
  core : pCoreOf 2 (K ⊔ R) ≤ R
  not_cent : ¬ K ≤ Subgroup.centralizer (V : Set G)

namespace StarHyp

variable {R K V : Subgroup G} (h : StarHyp R K V)
include h

theorem elemAbelian : IsElemAbelian 2 V := h.red.2.2.1

theorem le_normalizer : K ⊔ R ≤ Subgroup.normalizer (K : Set G) :=
  sup_le Subgroup.le_normalizer h.norm

theorem le_normalizer_V : K ⊔ R ≤ Subgroup.normalizer (V : Set G) := h.red.2.1

theorem K_le_normalizer_V : K ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans h.red.2.1

theorem R_le_normalizer_V : R ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans h.red.2.1

theorem mem_sup {x : G} : x ∈ K ⊔ R ↔ ∃ k ∈ K, ∃ r ∈ R, x = k * r :=
  B19Aux.mem_sup_iff_of_le_normalizer h.norm

theorem prod_of_le {T : Subgroup G} (hRT : R ≤ T) :
    ∀ x ∈ K ⊔ R, ∃ k ∈ K, ∃ t ∈ T, x = k * t := by
  intro x hx
  obtain ⟨k, hk, r, hr, rfl⟩ := h.mem_sup.1 hx
  exact ⟨k, hk, r, hRT hr, rfl⟩

theorem commutator_ne_bot : ⁅V, K⁆ ≠ ⊥ := by
  intro h0
  apply h.not_cent
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact h0

theorem le_normalizer_centralizer :
    K ⊔ R ≤ Subgroup.normalizer
      (((K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => ⟨(K ⊔ R).mul_mem ((K ⊔ R).mul_mem hx hc.1) ((K ⊔ R).inv_mem hx),
    C124.conj_mem_centralizer_of_le h.red.2.1 hx hc.2⟩, fun hc => ?_⟩
  have h1 := C124.conj_mem_centralizer_of_le h.red.2.1 ((K ⊔ R).inv_mem hx) hc.2
  refine ⟨?_, ?_⟩
  · have := (K ⊔ R).mul_mem ((K ⊔ R).mul_mem ((K ⊔ R).inv_mem hx) hc.1) hx
    simpa [mul_assoc] using this
  · simpa [mul_assoc] using h1

end StarHyp

end Basic

namespace StarHyp

variable {R K V : Subgroup G} (h : StarHyp R K V)
include h

theorem exists_sylow : ∃ T : Subgroup G, IsSylowTwoOf T (K ⊔ R) ∧ R ≤ T :=
  A4.exists_isSylowTwoOf_ge le_sup_right h.pgroup

theorem b2_10_2 {T : Subgroup G} (hT : IsSylowTwoOf T (K ⊔ R)) (hRT : R ≤ T) :
    (IsSylowTwoOf (pCoreOf 2 ((K ⊔ R) ⊓ Subgroup.centralizer (V : Set G)))
        ((K ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) ∧
      pCoreOf 2 (K ⊔ R) = R ⊓ Subgroup.centralizer (V : Set G)) ∧
    (CFSG.IsQuasisimple ↥(autI h.elemAbelian K) ∨ Nat.card ↥(autI h.elemAbelian K) = 3) ∧
    quasithinGenFitting (autI h.elemAbelian (K ⊔ R)) = autI h.elemAbelian K ∧
    (baum R = baum (pCoreOf 2 (K ⊔ R)) ∨
      (IsStableFF (autI h.elemAbelian (K ⊔ R))
          (C124.offenderImagesConjIn h.elemAbelian (K ⊔ R) R) ∧
        ffJP (C124.offenderImagesConjIn h.elemAbelian (K ⊔ R) R)
            (autI h.elemAbelian (K ⊔ R)) ≤ ffJ (autI h.elemAbelian (K ⊔ R)) ∧
        quasithinGenFitting (ffJP (C124.offenderImagesConjIn h.elemAbelian (K ⊔ R) R)
          (autI h.elemAbelian (K ⊔ R))) = autI h.elemAbelian K)) :=
  C124.B2_10_2 h.elemAbelian h.red h.core hRT hT le_sup_left h.le_normalizer
    (h.prod_of_le hRT) h.commutator_ne_bot (Or.inl h.quasi)

theorem pCore_le_centralizer : pCoreOf 2 (K ⊔ R) ≤ Subgroup.centralizer (V : Set G) :=
  C124.pCoreOf_le_centralizer h.red

theorem pCore_K_le_pCore : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
    (h.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)

theorem pCore_K_le_centralizer : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) :=
  h.pCore_K_le_pCore.trans h.pCore_le_centralizer

theorem centralizer_isSylow :
    IsSylowTwoOf (pCoreOf 2 (K ⊔ R)) ((K ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hRT⟩ := h.exists_sylow
  obtain ⟨⟨hsyl, -⟩, -⟩ := h.b2_10_2 hT hRT
  set C := (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) with hC
  have hle1 : pCoreOf 2 C ≤ pCoreOf 2 (K ⊔ R) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 C).trans inf_le_left)
      (h.le_normalizer_centralizer.trans (normalizer_le_normalizer_pCoreOf 2 C))
      (pCoreOf_isPGroup 2 C)
  have hle2 : pCoreOf 2 (K ⊔ R) ≤ pCoreOf 2 C :=
    le_pCoreOf_of_le_normalizer 2 (le_inf (pCoreOf_le 2 _) h.pCore_le_centralizer)
      (inf_le_left.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  rw [le_antisymm hle1 hle2] at hsyl
  exact hsyl

theorem pCore_eq_inf : pCoreOf 2 (K ⊔ R) = R ⊓ Subgroup.centralizer (V : Set G) := by
  obtain ⟨T, hT, hRT⟩ := h.exists_sylow
  exact (h.b2_10_2 hT hRT).1.2

theorem pCore_K_eq_bot : pCoreOf 2 (autOn K V) = ⊥ :=
  C124.pCoreOf_autI_L_eq_bot h.elemAbelian h.red le_sup_left h.le_normalizer

theorem pCore_eq_bot : pCoreOf 2 (autOn (K ⊔ R) V) = ⊥ :=
  C124.pCoreOf_autI_eq_bot h.elemAbelian h.red

theorem quasisimple : CFSG.IsQuasisimple ↥(autOn K V) :=
  InternalSec.isQuasisimple_autOn h.K_le_normalizer_V h.quasi h.pCore_K_eq_bot h.not_cent

theorem genFitting_eq : quasithinGenFitting (autOn (K ⊔ R) V) = autOn K V := by
  obtain ⟨T, hT, hRT⟩ := h.exists_sylow
  exact (h.b2_10_2 hT hRT).2.2.1

theorem inf_centralizer_le : K ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro c ⟨hcK, hcC⟩
  have hn : oTwoZIn K ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ R) : Set G) :=
    (oTwoZIn_le' K).trans (le_sup_left.trans (le_normalizer_pCoreOf 2 _))
  obtain ⟨q, hq, z, hz, rfl⟩ :=
    (B19Aux.mem_sup_iff_of_le_normalizer hn).1 (h.cent ⟨Subgroup.mem_sup_left hcK, hcC⟩)
  have hzK : z ∈ K := oTwoZIn_le' K hz
  have hqK : q ∈ K := by
    have := K.mul_mem hcK (K.inv_mem hzK)
    simpa using this
  have hKQ : K ⊓ pCoreOf 2 (K ⊔ R) ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hk, le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hk)⟩)
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
  exact (oTwoZIn K).mul_mem (pCore_le_oTwoZIn' K (hKQ ⟨hqK, hq⟩)) hz

theorem inf_centralizer_eq (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) :
    K ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 K := by
  refine le_antisymm ?_ (le_inf (pCoreOf_le 2 K) h.pCore_K_le_centralizer)
  rw [← oTwoZIn_eq_of_center_eq_bot hZ]
  exact h.inf_centralizer_le

theorem ker_autOnHom_eq (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) :
    (InternalSec.autOnHom h.K_le_normalizer_V).ker = CFSG.pCore 2 ↥K := by
  ext l
  rw [InternalSec.mem_ker_autOnHom]
  constructor
  · intro hl
    have h1 : (l : G) ∈ pCoreOf 2 K := (h.inf_centralizer_eq hZ).le ⟨l.2, hl⟩
    rw [C124.pCoreOf_eq_map_pCore] at h1
    obtain ⟨y, hy, hye⟩ := h1
    rwa [Subtype.ext hye] at hy
  · intro hl
    exact h.pCore_K_le_centralizer (by rw [C124.pCoreOf_eq_map_pCore]; exact ⟨l, hl, rfl⟩)

theorem quotEquiv (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(autOn K V)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (h.ker_autOnHom_eq hZ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (InternalSec.autOnHom_surjective h.K_le_normalizer_V))⟩

theorem autOn_inf_of_le {Y : Subgroup G} (hQY : pCoreOf 2 (K ⊔ R) ≤ Y) (hYX : Y ≤ K ⊔ R) :
    autOn Y V ⊓ autOn K V = autOn (Y ⊓ K) V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_inf (autOn_mono' inf_le_left) (autOn_mono' inf_le_right))
  rintro φ ⟨hY, hK⟩
  obtain ⟨y, hy, rfl⟩ := mem_autOn_iff'.1 hY
  obtain ⟨k, hk, hke⟩ := mem_autOn_iff'.1 hK
  have hyk : conjAct V (y * k⁻¹) = 1 := by rw [map_mul, map_inv, hke, mul_inv_cancel]
  have hc : (y : G) * (k : G)⁻¹ ∈ (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) :=
    ⟨(K ⊔ R).mul_mem (hYX hy) ((K ⊔ R).inv_mem (Subgroup.mem_sup_left hk)),
      (conjAct_eq_one_iff' _).1 hyk⟩
  have hn : oTwoZIn K ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ R) : Set G) :=
    (oTwoZIn_le' K).trans (le_sup_left.trans (le_normalizer_pCoreOf 2 _))
  obtain ⟨q, hq, z, hz, hqz⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hn).1 (h.cent hc)
  have hqN : q ∈ Subgroup.normalizer (V : Set G) := h.le_normalizer_V (pCoreOf_le 2 _ hq)
  have hqC : q ∈ Subgroup.centralizer (V : Set G) := h.pCore_le_centralizer hq
  have e : q⁻¹ * (y : G) = z * k := by
    have e1 : (y : G) = q * z * k := by rw [← hqz]; group
    rw [e1]; group
  refine mem_autOn_iff'.2 ⟨⟨q, hqN⟩⁻¹ * y, ⟨?_, ?_⟩, ?_⟩
  · show q⁻¹ * (y : G) ∈ Y
    exact Y.mul_mem (Y.inv_mem (hQY hq)) hy
  · show q⁻¹ * (y : G) ∈ K
    rw [e]
    exact K.mul_mem (oTwoZIn_le' K hz) hk
  · rw [map_mul, map_inv, (conjAct_eq_one_iff' ⟨q, hqN⟩).2 hqC, inv_one, one_mul]

theorem autOn_inf_R : autOn R V ⊓ autOn K V = autOn (R ⊓ K) V :=
  h.autOn_inf_of_le h.core le_sup_right

theorem autOn_inf_M {M : Subgroup G} (hRM : R ≤ M) :
    autOn (M ⊓ K) V = autOn (M ⊓ (K ⊔ R)) V ⊓ autOn K V := by
  rw [h.autOn_inf_of_le (Y := M ⊓ (K ⊔ R)) (le_inf (h.core.trans hRM) (pCoreOf_le 2 _))
    inf_le_right, inf_assoc, inf_eq_right.2 (le_sup_left : K ≤ K ⊔ R)]

theorem isSylowTwoOf_iff :
    IsSylowTwoOf R (K ⊔ R) ↔ IsSylowTwoOf (autOn R V) (autOn (K ⊔ R) V) := by
  refine isSylowTwoOf_iff_autOn h.le_normalizer_V le_sup_right h.pgroup ?_
  rw [← h.pCore_eq_inf]
  exact h.centralizer_isSylow

omit [Finite G] in
theorem autOn_sup : autOn (K ⊔ R) V = autOn K V ⊔ autOn R V := by
  refine le_antisymm ?_ (sup_le (autOn_mono' le_sup_left) (autOn_mono' le_sup_right))
  intro φ hφ
  obtain ⟨x, hx, rfl⟩ := mem_autOn_iff'.1 hφ
  obtain ⟨k, hk, r, hr, hkr⟩ := h.mem_sup.1 hx
  have hkN : k ∈ Subgroup.normalizer (V : Set G) := h.K_le_normalizer_V hk
  have hrN : r ∈ Subgroup.normalizer (V : Set G) := h.R_le_normalizer_V hr
  have e : x = ⟨k, hkN⟩ * ⟨r, hrN⟩ := Subtype.ext hkr
  rw [e, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_autOn_iff'.2 ⟨_, hk, rfl⟩))
    (Subgroup.mem_sup_right (mem_autOn_iff'.2 ⟨_, hr, rfl⟩))

omit [Finite G] in
theorem normalizes :
    autOn (K ⊔ R) V ≤ Subgroup.normalizer (autOn K V : Set (MulAut ↥V)) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨fun hl => C124.autI_conj_mem h.elemAbelian h.le_normalizer y hy l hl, fun hl => ?_⟩
  have h1 := C124.autI_conj_mem h.elemAbelian h.le_normalizer y⁻¹
    ((autOn (K ⊔ R) V).inv_mem hy) _ hl
  have e : l = y⁻¹ * (y * l * y⁻¹) * y⁻¹⁻¹ := by group
  rw [e]
  exact h1

theorem centralizer_le :
    autOn (K ⊔ R) V ⊓ Subgroup.centralizer (autOn K V : Set (MulAut ↥V)) ≤ autOn K V := by
  have := centralizer_quasithinGenFitting_le (autOn (K ⊔ R) V)
  rwa [h.genFitting_eq] at this

end StarHyp

end CFSG.Quasithin.SmithC27
