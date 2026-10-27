module

public import CFSG.Quasithin.MS93.S36Ext2
public import CFSG.Quasithin.MS93.S36Conj
public import CFSG.Quasithin.MS93.S36Ext1

public section

namespace CFSG.Quasithin.MS93.S36

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem card_sup_le_of_le_normalizer {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card ↥A * Nat.card ↥B := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right A B hAB
  calc Nat.card ↥(A ⊔ B) = Nat.card ((A : Set G) * (B : Set G)) := by rw [← h]; rfl
    _ ≤ Nat.card (A : Set G) * Nat.card (B : Set G) := Set.natCard_mul_le
    _ = Nat.card ↥A * Nat.card ↥B := rfl

theorem card_map_conj (K : Subgroup G) (g : G) :
    Nat.card ↥(K.map (MulAut.conj g).toMonoidHom) = Nat.card ↥K :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem mem_map_conj {K : Subgroup G} {g x : G} :
    x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [mul_assoc] using hk
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩

section Main

variable [Finite G] {M T L : Subgroup G} (h : PUHyp M T L) {F : Type} [Field F] [Fintype F]
  {a : ↥L →* ↥(StatedSL 3 F)} (N : NatSec L (Uq M T L) ⊥ a false)

omit [Fintype F] in
include h in
theorem Uq_le_Vq : Uq M T L ≤ Vq M L := Subgroup.commutator_mono h.Z0q_le_pCoreOf le_rfl

omit [Finite G] [Fintype F] in
include N in
theorem conj_eq_of_toSL3_eq_one {k : ↥L} (hk : toSL3 a k = 1) {y : G} (hy : y ∈ Uq M T L) :
    (k : G) * y * (k : G)⁻¹ = y := by
  refine N.eq_of_coord_eq (N.conj_mem k hy) hy ?_
  rw [N.coord_conj k hy, natAct_false, hk]
  simp

include h N in
theorem exists_t0 [CharP F 2] (ha : Function.Surjective a) {ψ : MulAut ↥T}
    (hR : Nat.card ↥⁅Z0q M T, tImage ψ (Z0q M T)⁆ = Fintype.card F)
    (hVQ : ⁅Vq M L, pCoreOf 2 M⁆ ≤ Uq M T L) :
    IsFClosed N ⁅Z0q M T, tImage ψ (Z0q M T)⁆ ∧
      ∃ t₀ ∈ L, (∀ u ∈ Uq M T L, t₀ * u * t₀⁻¹ * u⁻¹ ∈ ⁅Z0q M T, tImage ψ (Z0q M T)⁆) ∧
        (∃ u ∈ Uq M T L, t₀ * u * t₀⁻¹ ≠ u) ∧
        (∀ u ∈ Uq M T L, t₀ * t₀ * u * (t₀ * t₀)⁻¹ = u) ∧
        Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer ({t₀} : Set G)) =
          Fintype.card F * Fintype.card F ∧
        ∀ v ∈ Vq M L, t₀ * v * t₀⁻¹ * v⁻¹ ∈ ⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆ ⊔ Uq M T L := by
  set R := ⁅Z0q M T, tImage ψ (Z0q M T)⁆ with hRdef
  set q := Fintype.card F with hqdef
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hZT : Z0q M T ≤ T := Z0q_le_T h
  have hUT : Uq M T L ≤ T := (Uq_le_Z0q h.L_le).trans hZT
  have hTU := T_le_normalizer_Uq h
  have hUc := N.card_eq
  rw [Nat.card_eq_fintype_card (α := F)] at hUc
  have hcent := S33.inf_centralizer_Uq h
  have hBT : tImage ψ⁻¹ (Z0q M T) ≤ T := tImage_le _ _
  have hRUψ : R = ⁅Z0q M T, tImage ψ (Uq M T L)⁆ := by
    have h1 : tImage ψ ⁅Uq M T L, tImage ψ⁻¹ (Z0q M T)⁆ = ⁅tImage ψ (Uq M T L), Z0q M T⁆ := by
      rw [tImage_commutator ψ hUT hBT, tImage_tImage_inv ψ hZT]
    have h2 : tImage ψ ⁅Z0q M T, tImage ψ⁻¹ (Z0q M T)⁆ = ⁅tImage ψ (Z0q M T), Z0q M T⁆ := by
      rw [tImage_commutator ψ hZT hBT, tImage_tImage_inv ψ hZT]
    rw [hRdef, Subgroup.commutator_comm, ← h2, S33.commutator_Z0q_eq h hBT, h1,
      Subgroup.commutator_comm]
  obtain ⟨u', hu'U, hu'Q⟩ : ∃ u' ∈ tImage ψ (Uq M T L), u' ∉ pCoreOf 2 M := by
    by_contra hall
    push Not at hall
    have hbot : R = ⊥ := by
      rw [hRUψ, eq_bot_iff, Subgroup.commutator_le]
      intro z hz u hu
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (commute_of_mem_pCoreOf_Xq (hall u hu) (h.Z0q_le_Xq hz)).symm
    have : Nat.card ↥R = 1 := by rw [hbot]; exact Subgroup.card_bot
    omega
  have hu'T : u' ∈ T := tImage_le ψ _ hu'U
  have hu'2 : u' ^ 2 = 1 := sq_eq_one_of_mem_tImage h.isElemAbelian_Uq.2 hu'U
  set I := commImg (uq_comm h) (hTU hu'T) with hIdef
  have hIR : I ≤ R := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (mem_commImg _ _).mp hx
    rw [hRUψ, Subgroup.commutator_comm]
    have := Subgroup.commutator_mem_commutator hu'U (Uq_le_Z0q h.L_le hu)
    simpa [commutatorElement_def] using this
  obtain ⟨f, hf⟩ := exists_isCoordMap N (hTU hu'T)
  have hlin := linear_of_commImg_le h N ha hu'T hIR hR.le hf
  have hI1 : I ≠ ⊥ := by
    intro hbot
    apply hu'Q
    rw [← hcent]
    refine ⟨hu'T, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have : u' * u * u'⁻¹ * u⁻¹ ∈ I := (mem_commImg _ _).mpr ⟨u, hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    calc u * u' = (u' * u * u'⁻¹ * u⁻¹)⁻¹ * (u' * u) := by group
      _ = u' * u := by rw [this, inv_one, one_mul]
  have hIF := isFClosed_commImg (uq_comm h) (hTU hu'T) hf hlin
  have hIc : Nat.card ↥I = q := by
    refine le_antisymm ((Subgroup.card_le_of_le hIR).trans hR.le) ?_
    have := hIF.card_ge (commImg_le _ _) hI1
    rwa [Nat.card_eq_fintype_card] at this
  have hIeq : I = R := Subgroup.eq_of_le_of_card_ge hIR (by rw [hIc, hR])
  have hRF : IsFClosed N R := hIeq ▸ hIF
  have hCu' : Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer ({u'} : Set G)) = q * q := by
    have hm := card_commImg_mul (uq_comm h) (hTU hu'T)
    rw [← hIdef, hIc, hUc] at hm
    have hq0 : 0 < q := by omega
    exact Nat.eq_of_mul_eq_mul_left hq0 (by rw [hm]; ring)
  obtain ⟨l₁, hl₁⟩ := hf.exists_eq_conj ha (hTU hu'T) hlin (e := 1) (by rw [pow_one]; exact hu'2)
  have hcM : (l₁ : G)⁻¹ * u' ∈ M := M.mul_mem (M.inv_mem (h.L_le l₁.2)) (h.le hu'T)
  have hcU : ∀ u ∈ Uq M T L, (l₁ : G)⁻¹ * u' * u = u * ((l₁ : G)⁻¹ * u') := by
    intro u hu
    have h1 := hl₁ u hu
    calc (l₁ : G)⁻¹ * u' * u = (l₁ : G)⁻¹ * (u' * u * u'⁻¹) * u' := by group
      _ = (l₁ : G)⁻¹ * ((l₁ : G) * u * (l₁ : G)⁻¹) * u' := by rw [h1]
      _ = u * ((l₁ : G)⁻¹ * u') := by group
  obtain ⟨x, hxQ, hxL⟩ := exists_mul_inv_mem_L h hcM hcU
  set t₀ := u' * x⁻¹ with ht₀
  have ht₀L : t₀ ∈ L := by
    have : t₀ = (l₁ : G) * ((l₁ : G)⁻¹ * u' * x⁻¹) := by rw [ht₀]; group
    rw [this]
    exact L.mul_mem l₁.2 hxL
  have hxU : ∀ u ∈ Uq M T L, x * u = u * x := fun u hu =>
    commute_of_mem_pCoreOf_Xq hxQ (h.Uq_le_Xq hu)
  have ht₀u : ∀ u ∈ Uq M T L, t₀ * u * t₀⁻¹ = u' * u * u'⁻¹ := by
    intro u hu
    calc t₀ * u * t₀⁻¹ = u' * (x⁻¹ * u * x) * u'⁻¹ := by rw [ht₀]; group
      _ = u' * u * u'⁻¹ := by
          rw [show x⁻¹ * u * x = x⁻¹ * (x * u) by rw [hxU u hu]; group]
          group
  refine ⟨hRF, t₀, ht₀L, fun u hu => ?_, ?_, fun u hu => ?_, ?_, fun v hv => ?_⟩
  · rw [ht₀u u hu, ← hIeq]
    exact (mem_commImg _ _).mpr ⟨u, hu, rfl⟩
  · obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hI1
    obtain ⟨u, hu, hyu⟩ := (mem_commImg _ _).mp y.2
    refine ⟨u, hu, fun heq => hy1 (Subtype.ext ?_)⟩
    rw [← hyu, ← ht₀u u hu, heq, mul_inv_cancel]
    rfl
  · have hu1 := ht₀u u hu
    have hu2 := ht₀u _ (conj_mem_of_normalizer (hTU hu'T) hu)
    have hu'u' : u' * u' = 1 := by rw [← sq]; exact hu'2
    calc t₀ * t₀ * u * (t₀ * t₀)⁻¹ = t₀ * (t₀ * u * t₀⁻¹) * t₀⁻¹ := by group
      _ = u' * (u' * u * u'⁻¹) * u'⁻¹ := by rw [hu1, hu2]
      _ = (u' * u') * u * (u' * u')⁻¹ := by group
      _ = u := by rw [hu'u', one_mul, inv_one, mul_one]
  · have : Uq M T L ⊓ Subgroup.centralizer ({t₀} : Set G) =
        Uq M T L ⊓ Subgroup.centralizer ({u'} : Set G) := by
      ext u
      simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨hu, hc⟩
        refine ⟨hu, ?_⟩
        have h1 := ht₀u u hu
        rw [show t₀ * u * t₀⁻¹ = u by rw [← hc]; group] at h1
        calc u * u' = u' * u * u'⁻¹ * u' := by rw [← h1]
          _ = u' * u := by group
      · rintro ⟨hu, hc⟩
        refine ⟨hu, ?_⟩
        have h1 := ht₀u u hu
        rw [show u' * u * u'⁻¹ = u by rw [← hc]; group] at h1
        calc u * t₀ = t₀ * u * t₀⁻¹ * t₀ := by rw [h1]
          _ = t₀ * u := by group
    rw [this, hCu']
  · have hvQ : v ∈ pCoreOf 2 M := Vq_le_pCoreOf h.L_le hv
    have hw : ⁅v⁻¹, x⁻¹⁆ ∈ Uq M T L := hVQ (Subgroup.commutator_mem_commutator
      ((Vq M L).inv_mem hv) ((pCoreOf 2 M).inv_mem hxQ))
    have hvT : v ∈ T := h.pCore_le hvQ
    have h1 : u' * v * u'⁻¹ * v⁻¹ ∈ ⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆ := by
      have := Subgroup.commutator_mem_commutator hvQ
        (tImage_mono ψ (Uq_le_Z0q h.L_le) hu'U)
      rw [Subgroup.commutator_comm] at this
      have h2 := (⁅tImage ψ (Z0q M T), pCoreOf 2 M⁆).inv_mem this
      rw [Subgroup.commutator_comm]
      simpa [commutatorElement_def, mul_assoc] using h2
    have h3 : v * (u' * ⁅v⁻¹, x⁻¹⁆ * u'⁻¹) * v⁻¹ ∈ Uq M T L :=
      conj_mem_of_normalizer (hTU hvT) (conj_mem_of_normalizer (hTU hu'T) hw)
    rw [show t₀ * v * t₀⁻¹ * v⁻¹ = (u' * v * u'⁻¹ * v⁻¹) * (v * (u' * ⁅v⁻¹, x⁻¹⁆ * u'⁻¹) * v⁻¹) by
      rw [ht₀, commutatorElement_def]; group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h3)

omit [Fintype F] in
include h in
theorem conj_comm_mem_U {R : Subgroup G} {t₀ : G}
    (ht₀R : ∀ u ∈ Uq M T L, t₀ * u * t₀⁻¹ * u⁻¹ ∈ R) (m : G) (hm : m ∈ L) {y : G}
    (hy : y ∈ Uq M T L) :
    (m * t₀ * m⁻¹) * y * (m * t₀ * m⁻¹)⁻¹ * y⁻¹ ∈ R.map (MulAut.conj m).toMonoidHom := by
  have hy' : m⁻¹ * y * m⁻¹⁻¹ ∈ Uq M T L :=
    conj_mem_of_normalizer (le_normalizer_Uq h.le_normalizer (h.L_le (L.inv_mem hm))) hy
  rw [mem_map_conj]
  have := ht₀R _ hy'
  simpa [mul_assoc] using this

omit [Fintype F] in
include h in
theorem conj_comm_mem_V {H : Subgroup G} (hHM : H ≤ M) {t₀ : G}
    (ht₀V : ∀ v ∈ Vq M L, t₀ * v * t₀⁻¹ * v⁻¹ ∈ H ⊔ Uq M T L) (m : G) (hm : m ∈ L)
    (hs : m * t₀ * m⁻¹ ∈ L) {v : G} (hv : v ∈ Vq M L) :
    (m * t₀ * m⁻¹) * v * (m * t₀ * m⁻¹)⁻¹ * v⁻¹ ∈
      H.map (MulAut.conj m).toMonoidHom ⊓ Vq M L ⊔ Uq M T L := by
  have hVn := le_normalizer_Vq (M := M) h.le_normalizer
  have hUn := le_normalizer_Uq (T := T) h.le_normalizer
  have hmM := h.L_le hm
  have hv' : m⁻¹ * v * m⁻¹⁻¹ ∈ Vq M L :=
    (Subgroup.mem_normalizer_iff.mp (hVn (M.inv_mem hmM)) v).mp hv
  have h1 := ht₀V _ hv'
  have hHU : H ≤ Subgroup.normalizer (Uq M T L : Set G) := hHM.trans hUn
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right H (Uq M T L) hHU
  have h1' : t₀ * (m⁻¹ * v * m⁻¹⁻¹) * t₀⁻¹ * (m⁻¹ * v * m⁻¹⁻¹)⁻¹ ∈
      ((H ⊔ Uq M T L : Subgroup G) : Set G) := h1
  rw [hset] at h1'
  obtain ⟨x, hx, u, hu, hxu⟩ := h1'
  have hsv : (m * t₀ * m⁻¹) * v * (m * t₀ * m⁻¹)⁻¹ * v⁻¹ = (m * x * m⁻¹) * (m * u * m⁻¹) := by
    have : (m * t₀ * m⁻¹) * v * (m * t₀ * m⁻¹)⁻¹ * v⁻¹ =
        m * (t₀ * (m⁻¹ * v * m⁻¹⁻¹) * t₀⁻¹ * (m⁻¹ * v * m⁻¹⁻¹)⁻¹) * m⁻¹ := by group
    rw [this, ← hxu]
    group
  have hmu : m * u * m⁻¹ ∈ Uq M T L := conj_mem_of_normalizer (hUn hmM) hu
  have hsV : (m * t₀ * m⁻¹) * v * (m * t₀ * m⁻¹)⁻¹ * v⁻¹ ∈ Vq M L :=
    (Vq M L).mul_mem ((Subgroup.mem_normalizer_iff.mp (hVn (h.L_le hs)) v).mp hv)
      ((Vq M L).inv_mem hv)
  have hmxV : m * x * m⁻¹ ∈ Vq M L := by
    have : m * x * m⁻¹ = ((m * t₀ * m⁻¹) * v * (m * t₀ * m⁻¹)⁻¹ * v⁻¹) * (m * u * m⁻¹)⁻¹ := by
      rw [hsv]; group
    rw [this]
    exact (Vq M L).mul_mem hsV ((Vq M L).inv_mem (Uq_le_Vq h hmu))
  rw [hsv]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨?_, hmxV⟩) (Subgroup.mem_sup_right hmu)
  exact mem_map_conj.mpr (by simpa [mul_assoc] using hx)

include h N in
theorem not_le_sup_of_gen (ha : Function.Surjective a) {s₀ s₁ s₂ : ↥L}
    (hgen : Subgroup.closure ({s₀, s₁, s₂} : Set ↥L) ⊔ (toSL3 a).ker = ⊤)
    {P₀ P₁ P₂ A B : Subgroup G}
    (hs₀ : ∀ y ∈ Uq M T L, (s₀ : G) * y * (s₀ : G)⁻¹ * y⁻¹ ∈ P₀)
    (hs₁ : ∀ y ∈ Uq M T L, (s₁ : G) * y * (s₁ : G)⁻¹ * y⁻¹ ∈ P₁)
    (hs₂ : ∀ y ∈ Uq M T L, (s₂ : G) * y * (s₂ : G)⁻¹ * y⁻¹ ∈ P₂)
    (hAU : A ≤ Uq M T L) (hBU : B ≤ Uq M T L) (hAc : Nat.card ↥A ≤ Fintype.card F)
    (hBc : Nat.card ↥B ≤ Fintype.card F) (h0 : P₀ ≤ A ⊔ B) (h1 : P₁ ≤ A ⊔ B) (h2 : P₂ ≤ A ⊔ B)
    (hA1 : A ≠ ⊥) : False := by
  set E := A ⊔ B with hE
  have hEU : E ≤ Uq M T L := sup_le hAU hBU
  have hconj : ∀ (s : ↥L) (P : Subgroup G), P ≤ E →
      (∀ y ∈ Uq M T L, (s : G) * y * (s : G)⁻¹ * y⁻¹ ∈ P) → ∀ y ∈ E, (s : G) * y * (s : G)⁻¹ ∈ E :=
    fun s P hPE hs y hy => by
      have : (s : G) * y * (s : G)⁻¹ = ((s : G) * y * (s : G)⁻¹ * y⁻¹) * y := by group
      rw [this]
      exact E.mul_mem (hPE (hs y (hEU hy))) hy
  let K : Subgroup ↥L := subgroupOfMulClosed {l : ↥L | ∀ y ∈ E, (l : G) * y * (l : G)⁻¹ ∈ E}
    (fun y hy => by simpa using hy)
    (fun l hl k hk y hy => by
      have : ((l * k : ↥L) : G) * y * ((l * k : ↥L) : G)⁻¹ =
          (l : G) * ((k : G) * y * (k : G)⁻¹) * (l : G)⁻¹ := by
        simp only [Subgroup.coe_mul]; group
      rw [this]
      exact hl _ (hk y hy))
  have hSK : Subgroup.closure ({s₀, s₁, s₂} : Set ↥L) ≤ K := by
    rw [Subgroup.closure_le]
    rintro s (rfl | rfl | rfl)
    · exact hconj _ _ h0 hs₀
    · exact hconj _ _ h1 hs₁
    · exact hconj _ _ h2 hs₂
  have hkerK : (toSL3 a).ker ≤ K := fun k hk y hy => by
    rw [conj_eq_of_toSL3_eq_one N hk (hEU hy)]
    exact hy
  have hK : ∀ l : ↥L, ∀ y ∈ E, (l : G) * y * (l : G)⁻¹ ∈ E := by
    intro l y hy
    have : l ∈ K := by
      have := (sup_le hSK hkerK : _ ≤ K)
      rw [hgen] at this
      exact this (Subgroup.mem_top l)
    exact this y hy
  obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
  have hUE : Uq M T L ≤ E :=
    N.le_of_invariant ha hK (Subgroup.mem_sup_left hr) (hAU hr) fun h' => hr1 (Subtype.ext h')
  have hAB : A ≤ Subgroup.normalizer (B : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxy : ∀ y ∈ B, x * y * x⁻¹ = y := fun y hy => by
      rw [uq_comm h x (hAU hx) y (hBU hy), mul_inv_cancel_right]
    constructor
    · intro hy; rw [hxy y hy]; exact hy
    · intro hy
      have hyU : y ∈ Uq M T L := by
        have := uq_comm h x (hAU hx)
        have hy' : x * y * x⁻¹ ∈ Uq M T L := hBU hy
        have e : y = x⁻¹ * (x * y * x⁻¹) * x := by group
        rw [e]
        exact (Uq M T L).mul_mem ((Uq M T L).mul_mem ((Uq M T L).inv_mem (hAU hx)) hy') (hAU hx)
      have : x * y * x⁻¹ = y := by
        rw [uq_comm h x (hAU hx) y hyU, mul_inv_cancel_right]
      rw [← this]
      exact hy
  have hc := (Subgroup.card_le_of_le hUE).trans (card_sup_le_of_le_normalizer hAB)
  have hUc := N.card_eq
  rw [Nat.card_eq_fintype_card (α := F)] at hUc
  rw [hUc] at hc
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have := hc.trans (Nat.mul_le_mul hAc hBc)
  have h3 : Fintype.card F ^ 3 = Fintype.card F * (Fintype.card F * Fintype.card F) := by ring
  rw [h3] at this
  have h4 : 2 * (Fintype.card F * Fintype.card F) ≤ Fintype.card F * (Fintype.card F *
    Fintype.card F) := Nat.mul_le_mul_right _ hq
  have h5 : 0 < Fintype.card F * Fintype.card F := by positivity
  omega

omit [Fintype F] in
include h in
theorem comm_mem_conj {R H : Subgroup G} (hHQR : ⁅H, pCoreOf 2 M⁆ ≤ R) {m : G} (hm : m ∈ L)
    {x y : G} (hx : x ∈ H.map (MulAut.conj m).toMonoidHom) (hy : y ∈ Vq M L) :
    ⁅x, y⁆ ∈ R.map (MulAut.conj m).toMonoidHom := by
  have hVn := le_normalizer_Vq (M := M) h.le_normalizer
  have hy' : m⁻¹ * y * m⁻¹⁻¹ ∈ Vq M L :=
    (Subgroup.mem_normalizer_iff.mp (hVn (M.inv_mem (h.L_le hm))) y).mp hy
  have hx' : m⁻¹ * x * m ∈ H := mem_map_conj.mp hx
  rw [mem_map_conj]
  have := hHQR (Subgroup.commutator_mem_commutator hx' (Vq_le_pCoreOf h.L_le hy'))
  rw [show m⁻¹ * ⁅x, y⁆ * m = ⁅m⁻¹ * x * m, m⁻¹ * y * m⁻¹⁻¹⁆ by
    simp only [commutatorElement_def]; group]
  exact this

include h N in
theorem elem_and_card [CharP F 2] (ha : Function.Surjective a)
    (hU : IsSumOfNaturalModulesVia L (Uq M T L) ⊥ a false 1)
    {R H : Subgroup G} (hRU : R ≤ Uq M T L) (hRH : R ≤ H) (hRc : Nat.card ↥R = Fintype.card F)
    (hRF : IsFClosed N R) (hHQ : H ≤ pCoreOf 2 M)
    (hHc : Nat.card ↥H = Fintype.card F * Fintype.card F)
    (hHab : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hH2 : ∀ x ∈ H, x ^ 2 = 1)
    (hHQR : ⁅H, pCoreOf 2 M⁆ ≤ R) (hVQ : ⁅Vq M L, pCoreOf 2 M⁆ ≤ Uq M T L)
    {t₀ : G} (ht₀L : t₀ ∈ L) (ht₀R : ∀ u ∈ Uq M T L, t₀ * u * t₀⁻¹ * u⁻¹ ∈ R)
    (ht₀1 : ∃ u ∈ Uq M T L, t₀ * u * t₀⁻¹ ≠ u)
    (ht₀2 : ∀ u ∈ Uq M T L, t₀ * t₀ * u * (t₀ * t₀)⁻¹ = u)
    (ht₀C : Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer ({t₀} : Set G)) =
      Fintype.card F * Fintype.card F)
    (ht₀V : ∀ v ∈ Vq M L, t₀ * v * t₀⁻¹ * v⁻¹ ∈ H ⊔ Uq M T L) :
    (∀ x ∈ Vq M L, ∀ y ∈ Vq M L, x * y = y * x) ∧ (∀ x ∈ Vq M L, x ^ 2 = 1) ∧
      Nat.card ↥(Vq M L) ≤ Fintype.card F ^ 3 * Nat.card ↥(Uq M T L) := by
  set q := Fintype.card F with hqdef
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hHM : H ≤ M := hHQ.trans (pCoreOf_le' M)
  have hUn := le_normalizer_Uq (T := T) h.le_normalizer
  have hVn := le_normalizer_Vq (M := M) h.le_normalizer
  set t₀' : ↥L := ⟨t₀, ht₀L⟩ with ht₀'
  set γ := toSL3 a t₀' with hγ
  have hγ1 : γ ≠ 1 := by
    intro h1
    obtain ⟨u, hu, hne⟩ := ht₀1
    exact hne (conj_eq_of_toSL3_eq_one N h1 hu)
  have hγ2 : γ * γ = 1 := by
    have hα : a (t₀' * t₀') = 1 := alpha_eq_one_of_conj N fun v hv => by
      rw [Subgroup.mem_bot]
      simp only [Subgroup.coe_mul]
      rw [ht₀2 v hv, mul_inv_cancel]
    rw [hγ, ← map_mul]
    simp [toSL3, hα]
  have hfix : Nat.card F ^ 2 ≤ Nat.card ↥(KGNat.fixAdd
      (Matrix.mulVecLin ((γ : SL3 F) : Matrix (Fin 3) (Fin 3) F)).toAddMonoidHom) := by
    have hcm : IsCoordMap N t₀
        (Matrix.mulVecLin ((a t₀' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).toAddMonoidHom :=
      fun u hu => coord_conj_L t₀' hu
    have := hcm.card_fix (hUn (h.L_le ht₀L))
    rw [ht₀C] at this
    rw [hγ, coe_toSL3, ← this, Nat.card_eq_fintype_card, sq]
  obtain ⟨g', hg'⟩ := exists_conj_mem_rootGroup hγ1 hγ2 hfix
  obtain ⟨g, hg⟩ := toSL3_surjective ha g'
  set t : ↥L := g * t₀' * g⁻¹ with ht
  have htr : toSL3 a t ∈ rootGroup 0 2 := by
    rw [ht, map_mul, map_mul, map_inv, hg]
    exact hg'
  have ht1 : toSL3 a t ≠ 1 := by
    rw [ht, map_mul, map_mul, map_inv, hg]
    intro h1
    apply hγ1
    calc γ = g'⁻¹ * (g' * γ * g'⁻¹) * g' := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨g₁, g₂, hgen⟩ := ms11i_of_surjective (toSL3_surjective ha) htr ht1
  set m₁ : ↥L := g₁ * g with hm₁
  set m₂ : ↥L := g₂ * g with hm₂
  have hs₀ : ((t : ↥L) : G) = (g : G) * t₀ * (g : G)⁻¹ := by
    simp [ht, ht₀']
  have hs₁ : ((g₁ * t * g₁⁻¹ : ↥L) : G) = (m₁ : G) * t₀ * (m₁ : G)⁻¹ := by
    simp [ht, hm₁, ht₀']
    group
  have hs₂ : ((g₂ * t * g₂⁻¹ : ↥L) : G) = (m₂ : G) * t₀ * (m₂ : G)⁻¹ := by
    simp [ht, hm₂, ht₀']
    group
  set P₀ := R.map (MulAut.conj (g : G)).toMonoidHom with hP₀
  set P₁ := R.map (MulAut.conj (m₁ : G)).toMonoidHom with hP₁
  set P₂ := R.map (MulAut.conj (m₂ : G)).toMonoidHom with hP₂
  have hPU : ∀ m : ↥L, R.map (MulAut.conj (m : G)).toMonoidHom ≤ Uq M T L := by
    rintro m _ ⟨r, hr, rfl⟩
    exact conj_mem_of_normalizer (hUn (h.L_le m.2)) (hRU hr)
  have hPc : ∀ m : ↥L, Nat.card ↥(R.map (MulAut.conj (m : G)).toMonoidHom) = q := fun m => by
    rw [card_map_conj, hRc]
  have hPF : ∀ m : ↥L, IsFClosed N (R.map (MulAut.conj (m : G)).toMonoidHom) :=
    fun m => hRF.conj hRU m
  have hP1 : ∀ m : ↥L, R.map (MulAut.conj (m : G)).toMonoidHom ≠ ⊥ := fun m hbot => by
    have := hPc m
    rw [hbot, Subgroup.card_bot] at this
    omega
  have hsU₀ : ∀ y ∈ Uq M T L, ((t : ↥L) : G) * y * ((t : ↥L) : G)⁻¹ * y⁻¹ ∈ P₀ := by
    intro y hy; rw [hs₀]; exact conj_comm_mem_U h ht₀R _ g.2 hy
  have hsU₁ : ∀ y ∈ Uq M T L, ((g₁ * t * g₁⁻¹ : ↥L) : G) * y *
      ((g₁ * t * g₁⁻¹ : ↥L) : G)⁻¹ * y⁻¹ ∈ P₁ := by
    intro y hy; rw [hs₁]; exact conj_comm_mem_U h ht₀R _ m₁.2 hy
  have hsU₂ : ∀ y ∈ Uq M T L, ((g₂ * t * g₂⁻¹ : ↥L) : G) * y *
      ((g₂ * t * g₂⁻¹ : ↥L) : G)⁻¹ * y⁻¹ ∈ P₂ := by
    intro y hy; rw [hs₂]; exact conj_comm_mem_U h ht₀R _ m₂.2 hy
  have hdist : ∀ {A B C : Subgroup G} (hAeq : A = B), A ≤ Uq M T L → C ≤ Uq M T L →
      Nat.card ↥A ≤ q → Nat.card ↥C ≤ q → A ≠ ⊥ →
      ({P₀, P₁, P₂} : Set (Subgroup G)) ⊆ {A, B, C} → False := by
    intro A B C hAeq hAU hCU hAc hCc hA1 hsub
    have hle : ∀ P ∈ ({P₀, P₁, P₂} : Set (Subgroup G)), P ≤ A ⊔ C := by
      intro P hP
      rcases hsub hP with rfl | rfl | rfl
      · exact le_sup_left
      · rw [← hAeq]; exact le_sup_left
      · exact le_sup_right
    exact not_le_sup_of_gen h N ha hgen hsU₀ hsU₁ hsU₂ hAU hCU hAc hCc
      (hle _ (by simp)) (hle _ (by simp)) (hle _ (by simp)) hA1
  have hcF : ∀ m : ↥L, Nat.card ↥(R.map (MulAut.conj (m : G)).toMonoidHom) = Nat.card F :=
    fun m => by rw [hPc, Nat.card_eq_fintype_card]
  have hne : ∀ {A B : Subgroup G} (m m' : ↥L), A = R.map (MulAut.conj (m : G)).toMonoidHom →
      B = R.map (MulAut.conj (m' : G)).toMonoidHom → (A = B → False) → A ⊓ B = ⊥ := by
    intro A B m m' hA hB hAB
    by_contra hne
    obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    apply hAB
    rw [hA, hB]
    exact eq_of_isFClosed (hPF m) (hPF m') (hPU m) (hcF m) (hcF m') (hA ▸ hx.1) (hB ▸ hx.2)
      fun h' => hx1 (Subtype.ext h')
  have h01 : P₀ ⊓ P₁ = ⊥ := hne g m₁ rfl rfl fun heq =>
    hdist heq (hPU g) (hPU m₂) (hPc g).le (hPc m₂).le (hP1 g) fun P hP => hP
  have h02 : P₀ ⊓ P₂ = ⊥ := hne g m₂ rfl rfl fun heq =>
    hdist heq (hPU g) (hPU m₁) (hPc g).le (hPc m₁).le (hP1 g)
      (by intro P hP; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP ⊢; tauto)
  have h12 : P₁ ⊓ P₂ = ⊥ := hne m₁ m₂ rfl rfl fun heq =>
    hdist heq (hPU m₁) (hPU g) (hPc m₁).le (hPc g).le (hP1 m₁)
      (by intro P hP; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP ⊢; tauto)
  obtain ⟨E₀, hE₀⟩ : ∃ E, E = H.map (MulAut.conj (g : G)).toMonoidHom ⊓ Vq M L := ⟨_, rfl⟩
  obtain ⟨E₁, hE₁⟩ : ∃ E, E = H.map (MulAut.conj (m₁ : G)).toMonoidHom ⊓ Vq M L := ⟨_, rfl⟩
  obtain ⟨E₂, hE₂⟩ : ∃ E, E = H.map (MulAut.conj (m₂ : G)).toMonoidHom ⊓ Vq M L := ⟨_, rfl⟩
  obtain ⟨N₃, hN₃⟩ : ∃ N₃, N₃ = Uq M T L ⊔ E₀ ⊔ E₁ ⊔ E₂ := ⟨_, rfl⟩
  have hUV := Uq_le_Vq h
  have hE₀V : E₀ ≤ Vq M L := hE₀ ▸ inf_le_right
  have hE₁V : E₁ ≤ Vq M L := hE₁ ▸ inf_le_right
  have hE₂V : E₂ ≤ Vq M L := hE₂ ▸ inf_le_right
  have hN₃V : N₃ ≤ Vq M L := hN₃ ▸ sup_le (sup_le (sup_le hUV hE₀V) hE₁V) hE₂V
  have hUN₃ : Uq M T L ≤ N₃ := hN₃ ▸ le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hE₀N₃ : E₀ ≤ N₃ := hN₃ ▸ le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hE₁N₃ : E₁ ≤ N₃ := hN₃ ▸ le_sup_right.trans le_sup_left
  have hE₂N₃ : E₂ ≤ N₃ := hN₃ ▸ le_sup_right
  have hVQ' : Vq M L ≤ pCoreOf 2 M := Vq_le_pCoreOf h.L_le
  have hcommVQ : ∀ v ∈ Vq M L, ∀ n ∈ pCoreOf 2 M, ⁅v, n⁆ ∈ Uq M T L := fun v hv n hn =>
    hVQ (Subgroup.commutator_mem_commutator hv hn)
  have hgen' := closure_sup_pCore_eq_top h hU ha hgen
  obtain ⟨K, hK⟩ : ∃ K : Subgroup ↥L, ∀ l : ↥L,
      l ∈ K ↔ ∀ v ∈ Vq M L, (l : G) * v * (l : G)⁻¹ * v⁻¹ ∈ N₃ := by
    refine ⟨subgroupOfMulClosed {l : ↥L | ∀ v ∈ Vq M L, (l : G) * v * (l : G)⁻¹ * v⁻¹ ∈ N₃}
      (fun v _ => by simp) (fun l hl k hk v hv => ?_), fun l => Iff.rfl⟩
    have hn := hk v hv
    have hln : (l : G) * ((k : G) * v * (k : G)⁻¹ * v⁻¹) * (l : G)⁻¹ ∈ N₃ := by
      have h1 := hl _ (hN₃V hn)
      have : (l : G) * ((k : G) * v * (k : G)⁻¹ * v⁻¹) * (l : G)⁻¹ =
          ((l : G) * ((k : G) * v * (k : G)⁻¹ * v⁻¹) * (l : G)⁻¹ *
            ((k : G) * v * (k : G)⁻¹ * v⁻¹)⁻¹) * ((k : G) * v * (k : G)⁻¹ * v⁻¹) := by group
      rw [this]
      exact N₃.mul_mem h1 hn
    have : ((l * k : ↥L) : G) * v * ((l * k : ↥L) : G)⁻¹ * v⁻¹ =
        ((l : G) * ((k : G) * v * (k : G)⁻¹ * v⁻¹) * (l : G)⁻¹) *
          ((l : G) * v * (l : G)⁻¹ * v⁻¹) := by
      simp only [Subgroup.coe_mul]; group
    rw [this]
    exact N₃.mul_mem hln (hl v hv)
  have hsK : ∀ (s m : ↥L) (E : Subgroup G), (s : G) = (m : G) * t₀ * (m : G)⁻¹ →
      E = H.map (MulAut.conj (m : G)).toMonoidHom ⊓ Vq M L → E ≤ N₃ → s ∈ K := by
    intro s m E hsm hE hEN
    rw [hK]
    intro v hv
    have hs : (m : G) * t₀ * (m : G)⁻¹ ∈ L := L.mul_mem (L.mul_mem m.2 ht₀L) (L.inv_mem m.2)
    have := conj_comm_mem_V h hHM ht₀V m m.2 hs hv
    rw [← hE] at this
    rw [hsm]
    exact (sup_le hEN hUN₃) this
  have hSK : Subgroup.closure ({t, g₁ * t * g₁⁻¹, g₂ * t * g₂⁻¹} : Set ↥L) ≤ K := by
    rw [Subgroup.closure_le]
    rintro s (rfl | rfl | rfl)
    · exact hsK _ g E₀ hs₀ hE₀ hE₀N₃
    · exact hsK _ m₁ E₁ hs₁ hE₁ hE₁N₃
    · exact hsK _ m₂ E₂ hs₂ hE₂ hE₂N₃
  have hPK : CFSG.pCore 2 ↥L ≤ K := by
    intro o ho
    rw [hK]
    intro v hv
    have hoQ : (o : G) ∈ pCoreOf 2 M := pCoreOf_le_pCoreOf_of_le_normalizer h.L_le
      h.le_normalizer (mem_pCoreOf_of_mem_pCore_two ho)
    have h1 := hcommVQ v hv _ hoQ
    have h2 : (o : G) * v * (o : G)⁻¹ * v⁻¹ = ⁅v, (o : G)⁆⁻¹ := by
      rw [commutatorElement_def]; group
    rw [h2]
    exact hUN₃ ((Uq M T L).inv_mem h1)
  have hKtop : K = ⊤ := eq_top_iff.mpr (hgen' ▸ sup_le hSK hPK)
  have hVL : ⁅Vq M L, L⁆ ≤ N₃ := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    have hlK : (⟨l, hl⟩ : ↥L) ∈ K := by rw [hKtop]; exact Subgroup.mem_top _
    have hn := (hK _).mp hlK v⁻¹ ((Vq M L).inv_mem hv)
    simp only at hn
    have hnV := hN₃V hn
    have h1 : ⁅v, l⁆ = ⁅v, l * v⁻¹ * l⁻¹ * v⁻¹⁻¹⁆ * (l * v⁻¹ * l⁻¹ * v⁻¹⁻¹) := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rw [h1]
    exact N₃.mul_mem (hUN₃ (hcommVQ v hv _ (hVQ' hnV))) hn
  have hVeq : Vq M L = ⁅Vq M L, L⁆ :=
    commutator_eq_commutator_commutator (pCoreOf_le' M) h.L_le (le_normalizer_pCoreOf M)
      h.le_normalizer h.perfect
  have hVN₃ : Vq M L ≤ N₃ := hVeq ▸ hVL
  have hUc : ∀ u ∈ Uq M T L, ∀ v ∈ Vq M L, u * v = v * u := fun u hu v hv =>
    (commute_of_mem_pCoreOf_Xq (hVQ' hv) (h.Uq_le_Xq hu)).symm
  have hEab : ∀ (m : ↥L) (E : Subgroup G), E = H.map (MulAut.conj (m : G)).toMonoidHom ⊓ Vq M L →
      ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro m E hE x hx y hy
    rw [hE] at hx hy
    have hx' := mem_map_conj.mp hx.1
    have hy' := mem_map_conj.mp hy.1
    have := hHab _ hx' _ hy'
    calc x * y = (m : G) * (((m : G)⁻¹ * x * m) * ((m : G)⁻¹ * y * m)) * (m : G)⁻¹ := by group
      _ = (m : G) * (((m : G)⁻¹ * y * m) * ((m : G)⁻¹ * x * m)) * (m : G)⁻¹ := by rw [this]
      _ = y * x := by group
  have hEsq : ∀ (m : ↥L) (E : Subgroup G), E = H.map (MulAut.conj (m : G)).toMonoidHom ⊓ Vq M L →
      ∀ x ∈ E, x ^ 2 = 1 := by
    intro m E hE x hx
    rw [hE] at hx
    have hx' := hH2 _ (mem_map_conj.mp hx.1)
    calc x ^ 2 = (m : G) * ((m : G)⁻¹ * x * m) ^ 2 * (m : G)⁻¹ := by rw [sq, sq]; group
      _ = 1 := by rw [hx']; group
  have hcross : ∀ (m m' : ↥L) (E E' : Subgroup G),
      E = H.map (MulAut.conj (m : G)).toMonoidHom ⊓ Vq M L →
      E' = H.map (MulAut.conj (m' : G)).toMonoidHom ⊓ Vq M L →
      R.map (MulAut.conj (m : G)).toMonoidHom ⊓ R.map (MulAut.conj (m' : G)).toMonoidHom = ⊥ →
      ∀ x ∈ E, ∀ y ∈ E', x * y = y * x := by
    intro m m' E E' hE hE' hinf x hx y hy
    rw [hE] at hx
    rw [hE'] at hy
    have h1 := comm_mem_conj h hHQR m.2 hx.1 hy.2
    have h2 := comm_mem_conj h hHQR m'.2 hy.1 hx.2
    have h3 : ⁅x, y⁆ ∈ R.map (MulAut.conj (m : G)).toMonoidHom ⊓
        R.map (MulAut.conj (m' : G)).toMonoidHom := by
      refine ⟨h1, ?_⟩
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ h2
    rw [hinf, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3
  have h10 : P₁ ⊓ P₀ = ⊥ := by rw [inf_comm]; exact h01
  have h20 : P₂ ⊓ P₀ = ⊥ := by rw [inf_comm]; exact h02
  have h21 : P₂ ⊓ P₁ = ⊥ := by rw [inf_comm]; exact h12
  set S' : Set G := (Uq M T L : Set G) ∪ E₀ ∪ E₁ ∪ E₂ with hS'
  have hS'N₃ : Subgroup.closure S' = N₃ := by
    rw [hS', Subgroup.closure_union, Subgroup.closure_union, Subgroup.closure_union,
      Subgroup.closure_eq, Subgroup.closure_eq, Subgroup.closure_eq, Subgroup.closure_eq, hN₃]
  have hS'V : ∀ x ∈ S', x ∈ Vq M L := by
    rintro x (((hx | hx) | hx) | hx)
    · exact hUV hx
    · exact hE₀V hx
    · exact hE₁V hx
    · exact hE₂V hx
  have hcommS : ∀ x ∈ S', ∀ y ∈ S', x * y = y * x := by
    intro x hx y hy
    have hxV := hS'V x hx
    have hyV := hS'V y hy
    rcases hx with ((hx | hx) | hx) | hx
    · exact hUc x hx y hyV
    all_goals rcases hy with ((hy | hy) | hy) | hy
    all_goals first
      | exact (hUc y hy x hxV).symm
      | exact hEab g E₀ hE₀ x hx y hy
      | exact hEab m₁ E₁ hE₁ x hx y hy
      | exact hEab m₂ E₂ hE₂ x hx y hy
      | exact hcross g m₁ E₀ E₁ hE₀ hE₁ h01 x hx y hy
      | exact hcross g m₂ E₀ E₂ hE₀ hE₂ h02 x hx y hy
      | exact hcross m₁ g E₁ E₀ hE₁ hE₀ h10 x hx y hy
      | exact hcross m₁ m₂ E₁ E₂ hE₁ hE₂ h12 x hx y hy
      | exact hcross m₂ g E₂ E₀ hE₂ hE₀ h20 x hx y hy
      | exact hcross m₂ m₁ E₂ E₁ hE₂ hE₁ h21 x hx y hy
  have hsqS : ∀ x ∈ S', x ^ 2 = 1 := by
    rintro x (((hx | hx) | hx) | hx)
    · exact h.isElemAbelian_Uq.2 x hx
    · exact hEsq g E₀ hE₀ x hx
    · exact hEsq m₁ E₁ hE₁ x hx
    · exact hEsq m₂ E₂ hE₂ x hx
  obtain ⟨hc, hsq⟩ := elem_of_closure hcommS hsqS
  rw [hS'N₃] at hc hsq
  have hVc : ∀ x ∈ Vq M L, ∀ y ∈ Vq M L, x * y = y * x := fun x hx y hy =>
    hc x (hVN₃ hx) y (hVN₃ hy)
  refine ⟨hVc, fun x hx => hsq x (hVN₃ hx), ?_⟩
  have hEcard : ∀ (m : ↥L) (E : Subgroup G), E = H.map (MulAut.conj (m : G)).toMonoidHom ⊓ Vq M L →
      Nat.card ↥E ≤ q * Nat.card ↥(E ⊓ Uq M T L) := by
    intro m E hE
    have h1 : Nat.card ↥E ≤ q * q := by
      rw [← hHc, ← card_map_conj H (m : G), hE]
      exact Subgroup.card_le_of_le inf_le_left
    have h2 : q ≤ Nat.card ↥(E ⊓ Uq M T L) := by
      rw [← hPc m]
      refine Subgroup.card_le_of_le (le_inf ?_ (hPU m))
      rw [hE]
      exact le_inf (Subgroup.map_mono hRH) ((hPU m).trans hUV)
    exact h1.trans (Nat.mul_le_mul_left _ h2)
  exact card_le_of_le_sup hVc hUV hE₀V hE₁V hE₂V (hN₃ ▸ hVN₃) (hEcard g E₀ hE₀)
    (hEcard m₁ E₁ hE₁) (hEcard m₂ E₂ hE₂)

end Main

end CFSG.Quasithin.MS93.S36
