module

public import CFSG.Quasithin.Background.AutOnBasics
public import CFSG.Quasithin.Vol2.GoldschmidtCh7NormalConj
public import CFSG.Quasithin.Vol2.GoldschmidtCh7NormalGroup
public import CFSG.Quasithin.H13.StatementsCh7
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.Background.BlueprintB2Reduced

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem_ch7 {X : Subgroup G} {g : G}
    (h : ∀ y ∈ X, g * y * g⁻¹ ∈ X) : g ∈ Subgroup.normalizer (X : Set G) := by
  have hsub : X.map (MulAut.conj g).toMonoidHom ≤ X := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using h y hy
  have heq : X.map (MulAut.conj g).toMonoidHom = X :=
    Subgroup.eq_of_le_of_card_ge hsub (by
      have : Nat.card (X.map (MulAut.conj g).toMonoidHom) = Nat.card X :=
        Subgroup.card_map_of_injective (MulAut.conj g).injective
      omega)
  exact A38.map_conj_eq_iff.mp heq

theorem fsuL0_le_normalizer_fsuV {T L I : Subgroup G} (hF : FSU G T L I) :
    fsuL0 T L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
  have hN : fsuL0 T L ≤ Subgroup.normalizer (I : Set G) := hF.irrPlus.2.2.1
  intro l hl
  refine mem_normalizer_of_conj_mem_ch7 fun y hy => ?_
  change y ∈ Subgroup.closure _ at hy
  induction hy using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨s, hs, z, hz, rfl⟩ := hg
    have hl' : s⁻¹ * l * s ∈ fsuL0 T L := by
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_conjClosure L T (T.inv_mem hs)) l).mp hl
      simpa using this
    have hz' : (s⁻¹ * l * s) * z * (s⁻¹ * l * s)⁻¹ ∈ I :=
      (Subgroup.mem_normalizer_iff.mp (hN hl') z).mp hz
    have e : l * (s * z * s⁻¹) * l⁻¹ = s * ((s⁻¹ * l * s) * z * (s⁻¹ * l * s)⁻¹) * s⁻¹ := by
      group
    rw [e]
    exact mem_conjClosure hs hz'
  | one => simp
  | mul a b _ _ ha hb => simpa [mul_assoc] using (conjClosure I T).mul_mem ha hb
  | inv a _ ha => simpa [mul_assoc] using (conjClosure I T).inv_mem ha

theorem conj_mem_reducedAggregate {X : Subgroup G} {x y : G} (hx : x ∈ X)
    (hy : y ∈ reducedAggregate X) : x * y * x⁻¹ ∈ reducedAggregate X := by
  obtain ⟨y', hy', rfl⟩ := hy
  have hn := (isPrimeReduced_primeReducedAggregate (E := ↥X) 2).normal
  exact ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹, hn.conj_mem y' hy' ⟨x, hx⟩, by simp⟩

theorem pCoreOf_le_centralizer_reducedAggregate (X : Subgroup G) :
    pCoreOf 2 X ≤ Subgroup.centralizer (reducedAggregate X : Set G) := by
  intro p hp
  obtain ⟨p', hp', rfl⟩ := hp
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨y', hy', rfl⟩ := hy
  have hp'C : p' ∈ CFSG.pCore 2 ↥X := by assumption
  have h1 := Subgroup.mem_centralizer_iff.mp
    (pCore_le_centralizer_of_isPrimeReduced
      (isPrimeReduced_primeReducedAggregate (E := ↥X) 2) hp'C) y' hy'
  exact congrArg Subtype.val h1

theorem fsuV_le_reducedAggregate {T L I : Subgroup G} (hF : FSU G T L I) :
    fsuV T I ≤ reducedAggregate (L ⊔ T) :=
  conjClosure_le fun _ hs _ hz =>
    conj_mem_reducedAggregate (Subgroup.mem_sup_right hs) (hF.irrPlus.1 hz)

theorem pCoreOf_sup_le_centralizer_of_fsu {T L I : Subgroup G} (hF : FSU G T L I) :
    pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (fsuV T I : Set G) :=
  le_trans (pCoreOf_le_centralizer_reducedAggregate (L ⊔ T))
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (fsuV_le_reducedAggregate hF)))

theorem not_le_centralizer_of_fsu {T L I : Subgroup G} (hF : FSU G T L I) :
    ¬ L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  intro hL
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_normalizer_conjClosure I T
  have hI : I ≤ fsuV T I := le_conjClosure I T
  have h0 : fsuL0 T L ≤ Subgroup.centralizer (I : Set G) := by
    refine conjClosure_le fun s hs l hl => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : s⁻¹ * z * s ∈ fsuV T I := by
      have := (Subgroup.mem_normalizer_iff.mp (hTV (T.inv_mem hs)) z).mp (hI hz)
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp (hL hl) (s⁻¹ * z * s) hz'
    calc z * (s * l * s⁻¹) = s * ((s⁻¹ * z * s) * l) * s⁻¹ := by group
      _ = s * (l * (s⁻¹ * z * s)) * s⁻¹ := by rw [hc]
      _ = s * l * s⁻¹ * z := by group
  have h1 : ⁅I, fsuL0 T L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h0
  have h2 := hF.irrPlus.2.2.2.1
  rw [h1] at h2
  exact hF.irrPlus.2.1 h2.symm

theorem not_le_centralizer_conjSub_of_fsu {T L I : Subgroup G} (hF : FSU G T L I) {t : G}
    (htT : t ∈ T) : ¬ conjSub t L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  intro h
  apply not_le_centralizer_of_fsu hF
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : t * v * t⁻¹ ∈ fsuV T I :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure I T htT) v).mp hv
  have hc := Subgroup.mem_centralizer_iff.mp (h (⟨l, hl, rfl⟩ : t * l * t⁻¹ ∈ conjSub t L))
    (t * v * t⁻¹) hv'
  calc v * l = t⁻¹ * ((t * v * t⁻¹) * (t * l * t⁻¹)) * t := by group
    _ = t⁻¹ * ((t * l * t⁻¹) * (t * v * t⁻¹)) * t := by rw [hc]
    _ = l * v := by group

omit [Finite G] in
theorem autOn_sup_of_le {X Y V : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hY : Y ≤ Subgroup.normalizer (V : Set G)) :
    autOn (X ⊔ Y) V = autOn X V ⊔ autOn Y V :=
  CFSG.Quasithin.AutOn.autOn_sup_eq hX hY

omit [Finite G] in
theorem le_centralizer_of_subgroupOf_le_center {K L₀ V : Subgroup G} (hKL : K ≤ L₀)
    (hL₀ : L₀ ≤ Subgroup.normalizer (V : Set G)) (hK : ⁅K, K⁆ = K)
    (h : (autOn K V).subgroupOf (autOn L₀ V) ≤ Subgroup.center ↥(autOn L₀ V)) :
    K ≤ Subgroup.centralizer (V : Set G) := by
  have hnorm : ∀ k : G, k ∈ K → k ∈ Subgroup.normalizer (V : Set G) := fun k hk => hL₀ (hKL hk)
  have hA₁ : ∀ (k : G) (hk : k ∈ K), conjAct V ⟨k, hnorm k hk⟩ ∈ autOn K V := fun k hk =>
    Subgroup.mem_map.mpr ⟨⟨k, hnorm k hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hA₀ : ∀ (k : G) (hk : k ∈ K), conjAct V ⟨k, hnorm k hk⟩ ∈ autOn L₀ V := fun k hk =>
    Subgroup.mem_map.mpr ⟨⟨k, hnorm k hk⟩, Subgroup.mem_subgroupOf.mpr (hKL hk), rfl⟩
  rw [← hK]
  refine Subgroup.commutator_le.mpr fun k₁ hk₁ k₂ hk₂ => ?_
  set n₁ : ↥(Subgroup.normalizer (V : Set G)) := ⟨k₁, hnorm k₁ hk₁⟩ with hn₁
  set n₂ : ↥(Subgroup.normalizer (V : Set G)) := ⟨k₂, hnorm k₂ hk₂⟩ with hn₂
  have hcen := Subgroup.mem_center_iff.mp
    (h (Subgroup.mem_subgroupOf.mpr (hA₁ k₁ hk₁) :
      (⟨conjAct V n₁, hA₀ k₁ hk₁⟩ : ↥(autOn L₀ V)) ∈ (autOn K V).subgroupOf (autOn L₀ V)))
    ⟨conjAct V n₂, hA₀ k₂ hk₂⟩
  have hc : conjAct V n₂ * conjAct V n₁ = conjAct V n₁ * conjAct V n₂ := congrArg Subtype.val hcen
  have h1 : conjAct V (n₁ * n₂ * n₁⁻¹ * n₂⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    calc conjAct V n₁ * conjAct V n₂ * (conjAct V n₁)⁻¹ * (conjAct V n₂)⁻¹
        = (conjAct V n₂ * conjAct V n₁) * (conjAct V n₁)⁻¹ * (conjAct V n₂)⁻¹ := by rw [hc]
      _ = 1 := by group
  have h2 := A4.conjAct_eq_one_iff.mp h1
  have e : ((n₁ * n₂ * n₁⁻¹ * n₂⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) = ⁅k₁, k₂⁆ := by
    simp [commutatorElement_def, hn₁, hn₂]
  rwa [e] at h2

theorem false_of_not_normalizes {T L I : Subgroup G} (hF : FSU G T L I) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) {t : G} (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set G))
    (hmodel : ∃ (Γ : Type) (_ : Group Γ) (π : Γ →* ↥(autOn (fsuL0 T L) (fsuV T I))),
      Function.Surjective π ∧ NormalDichotomy Γ) : False := by
  obtain ⟨hcl, hcomm, hLt⟩ := fsu_conj_structure hF h37 h38 htT htL
  have hLc : L ∈ cComp (L ⊔ T) := hF.maximal.1.2.1
  have hL0V := fsuL0_le_normalizer_fsuV hF
  have hLL0 : L ≤ fsuL0 T L := le_conjClosure L T
  have hLtL0 : conjSub t L ≤ fsuL0 T L := by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_conjClosure htT hz
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := hLL0.trans hL0V
  have hLtV : conjSub t L ≤ Subgroup.normalizer (fsuV T I : Set G) := hLtL0.trans hL0V
  have hcentral : ⁅L, conjSub t L⁆ ≤ Subgroup.centralizer (fsuV T I : Set G) :=
    hcomm.trans (pCoreOf_sup_le_centralizer_of_fsu hF)
  have hcomm' := A4.autOn_le_centralizer_autOn (V := fsuV T I) hcentral
  have hA : autOn (fsuL0 T L) (fsuV T I) =
      autOn L (fsuV T I) ⊔ autOn (conjSub t L) (fsuV T I) := by
    unfold fsuL0
    rw [hcl]
    exact autOn_sup_of_le hLV hLtV
  obtain ⟨Γ, _, π, hπ, hQ⟩ := hmodel
  have h1 : autOn L (fsuV T I) ≤ autOn (fsuL0 T L) (fsuV T I) := by
    rw [hA]
    exact le_sup_left
  have h2 : autOn (conjSub t L) (fsuV T I) ≤ autOn (fsuL0 T L) (fsuV T I) := by
    rw [hA]
    exact le_sup_right
  refine false_of_commuting_pair π hπ hQ
    (A₁ := (autOn L (fsuV T I)).subgroupOf (autOn (fsuL0 T L) (fsuV T I)))
    (A₂ := (autOn (conjSub t L) (fsuV T I)).subgroupOf (autOn (fsuL0 T L) (fsuV T I)))
    ?_ ?_ ?_ ?_
  · rw [← Subgroup.subgroupOf_sup h1 h2, ← hA]
    exact Subgroup.subgroupOf_self _
  · intro a ha b hb
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hcomm' (Subgroup.mem_subgroupOf.mp hb)) a
      (Subgroup.mem_subgroupOf.mp ha)
  · intro hc
    exact not_le_centralizer_of_fsu hF
      (le_centralizer_of_subgroupOf_le_center hLL0 hL0V (perfect_of_mem_cComp hLc) hc)
  · intro hc
    exact not_le_centralizer_conjSub_of_fsu hF htT
      (le_centralizer_of_subgroupOf_le_center hLtL0 hL0V (perfect_of_mem_cComp hLt) hc)

end CFSG.Quasithin.H13
