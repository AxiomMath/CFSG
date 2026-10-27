module

public import CFSG.RankThree.GF2n.Smith81.S81LGen
public import CFSG.RankThree.GF2n.Smith81.S81CS8
public import CFSG.RankThree.GF2n.Smith81.Sec220Conj
public import CFSG.RankThree.GF2n.Smith81.S81CCases
public import CFSG.RankThree.GF2n.Smith81.Sec2Stmt

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def E3L45S5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (z v : G), E3L45World M Q Z B z v →
    ∀ t : G, IsConj z t → t ∈ Qv Q v →
      ∃ c ∈ Cv v, t ∈ conjSubgroup c Z ∧ conjSubgroup c Z ≤ Qv Q v

section Lemma4A2

variable [Finite G] {M Q Z : Subgroup G}

private theorem exists_mul_of_mem_sup {A K : Subgroup G}
    (hc : ∀ a ∈ A, ∀ k ∈ K, a * k = k * a) {x : G} (hx : x ∈ A ⊔ K) :
    ∃ a ∈ A, ∃ k ∈ K, a * k = x := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ k ∈ K, a * k = x}
      one_mem' := ⟨1, A.one_mem, 1, K.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, k₁, hk₁, rfl⟩ ⟨a₂, ha₂, k₂, hk₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
        have h := hc a₂ ha₂ k₁ hk₁
        calc a₁ * a₂ * (k₁ * k₂) = a₁ * (a₂ * k₁) * k₂ := by group
          _ = a₁ * (k₁ * a₂) * k₂ := by rw [h]
          _ = a₁ * k₁ * (a₂ * k₂) := by group
      inv_mem' := by
        rintro _ ⟨a, ha, k, hk, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, k⁻¹, K.inv_mem hk, ?_⟩
        have h := hc a ha k hk
        calc a⁻¹ * k⁻¹ = (k * a)⁻¹ := by group
          _ = (a * k)⁻¹ := by rw [h] }
  have hle : A ⊔ K ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, K.one_mem, mul_one a⟩)
      (fun k hk => ⟨1, A.one_mem, k, hk, one_mul k⟩)
  exact hle hx

theorem sit_mem_BlockOf_of_rootPoint (Hs : StrothHyp M Q Z) {z v t : G} {T : Subgroup G}
    (hz : z ∈ Z) (hvH : v ∈ H0 M Z) (hodd : Odd (orderOf v))
    (hS5 : ∀ t' : G, IsConj z t' → t' ∈ Qv Q v →
      ∃ c ∈ Cv v, t' ∈ conjSubgroup c Z ∧ conjSubgroup c Z ≤ Qv Q v)
    (hT : Sit M Q Z T t) (ht : IsConj z t) (htC : t ∈ Cv v)
    (h212 : (Q ⊓ QB T) ⊔ Z = ⁅Q, Subgroup.zpowers t⁆ ⊔ Z)
    (hRP : ∃ s : G, IsConj z s ∧ s ∈ Qv Q v ∧ s ∉ Z ∧ s ∈ ⁅Q, Subgroup.zpowers t⁆ ⊔ Z) :
    T ∈ BlockOf (Cv v) Z v := by
  have hvM : v ∈ M := hvH.1
  have hvZ' : ∀ a ∈ Z, a * v = v * a := fun a ha => Subgroup.mem_centralizer_iff.mp hvH.2 a ha
  have hvZ : ∀ a ∈ Z, v * a * v⁻¹ = a := fun a ha => by
    rw [← hvZ' a ha]
    group
  have hTZ : IsZConjugate Z T := hT.conj
  have ht1 : t ≠ 1 := hT.ne_one
  have h12 : Post12 M Q Z T := smith_1_12 hT
  have hTQ : T ⊓ Q = ⊥ := h12.2
  have hvt : Commute v t := (mem_Cv.mp htC).symm
  have hvNT : v ∈ Subgroup.normalizer (T : Set G) :=
    hTZ.mem_normalizer_of_commute Hs ht1 hT.mem hvt
  obtain ⟨s, hsz, hsQv, hsZ, hsJ⟩ := hRP
  rw [← h212] at hsJ
  obtain ⟨r, hrA, z', hz', hrs⟩ := exists_mul_of_mem_sup (A := Q ⊓ QB T) (K := Z)
    (fun a ha k hk => (Z_central Hs hk ha.1).symm) hsJ
  have hrQ : r ∈ Q := hrA.1
  have hrQT : r ∈ QB T := hrA.2
  have hsC : s * v = v * s := mem_Cv.mp hsQv.2
  have hvr : v * r * v⁻¹ = r := by
    have h1 : v * s * v⁻¹ = s := by
      rw [← hsC]
      group
    have h3 : v * (r * z') * v⁻¹ = (v * r * v⁻¹) * (v * z' * v⁻¹) := by group
    rw [hrs, h1, hvZ z' hz'] at h3
    have h4 : v * r * v⁻¹ * z' = r * z' := by rw [hrs]; exact h3.symm
    exact mul_right_cancel h4
  have hrC : r ∈ Cv v := by
    rw [mem_Cv]
    calc r * v = (v * r * v⁻¹) * v := by rw [hvr]
      _ = v * r := by group
  have hrZ : r ∉ Z := fun hr => hsZ (by rw [← hrs]; exact Z.mul_mem hr hz')
  have hr1 : r ≠ 1 := fun h1 => hrZ (h1 ▸ Z.one_mem)
  have hrconj : IsConj z r := by
    obtain ⟨x, hxQv, hx⟩ := exists_comm_eq_of_mem_Qv Hs hvH hodd hsQv hsZ (Z.inv_mem hz')
    have e : x * s * x⁻¹ = r := by
      have h1 : x * s * x⁻¹ = ⁅x, s⁆ * s := by
        rw [commutatorElement_def]
        group
      have hc : z' * r = r * z' := Z_central Hs hz' hrQ
      rw [h1, hx, ← hrs]
      calc z'⁻¹ * (r * z') = z'⁻¹ * (z' * r) := by rw [hc]
        _ = r := by group
    exact hsz.trans (isConj_iff.mpr ⟨x, e⟩)
  obtain ⟨gr, hgr⟩ := isConj_iff.mp hrconj
  have hRZ : IsZConjugate Z (conjSubgroup gr Z) := ⟨gr, rfl⟩
  have hrR : r ∈ conjSubgroup gr Z := by
    have e : gr⁻¹ * r * gr = z := by
      rw [← hgr]
      group
    rw [mem_conjSubgroup, e]
    exact hz
  have hRQ : conjSubgroup gr Z ≤ Q := by
    have := IsZConjugate.le_QB_of_mem Hs (IsZConjugate.self Z) hRZ hr1 hrR
      (by rw [Hs.QB_Z]; exact hrQ)
    rwa [Hs.QB_Z] at this
  have hRQT : conjSubgroup gr Z ≤ QB T := IsZConjugate.le_QB_of_mem Hs hTZ hRZ hr1 hrR hrQT
  have hRZne : conjSubgroup gr Z ≠ Z := fun e => hrZ (e ▸ hrR)
  have hvNR : v ∈ Subgroup.normalizer ((conjSubgroup gr Z : Subgroup G) : Set G) :=
    hRZ.mem_normalizer_of_commute Hs hr1 hrR (mem_Cv.mp hrC).symm
  have hRC : conjSubgroup gr Z ≤ Cv v :=
    le_Cv_of_fixed_mem ⟨Hs, ⟨gr, rfl⟩, hRQ, hRZne⟩ hvM hvZ hvNR hrR hrZ hvr
  obtain ⟨c, hc, hrc, -⟩ := hS5 r hrconj ⟨hrQ, hrC⟩
  have hRc : conjSubgroup gr Z = conjSubgroup c Z :=
    IsZConjugate.eq_of_mem Hs hRZ ⟨c, rfl⟩ hr1 hrR hrc
  have hRZC : conjSubgroup gr Z ∈ ZConjBy (Cv v) Z := ⟨c, hc, hRc⟩
  have hRblock : conjSubgroup gr Z ∈ BlockOf (Cv v) Z v := by
    refine Relation.EqvGen.rel _ _ ⟨ZConjBy.self _, hRZC, ?_⟩
    show conjSubgroup gr Z ≤ QB Z ⊓ Cv v
    rw [Hs.QB_Z]
    exact le_inf hRQ hRC
  have hTQR : T ≤ QB (conjSubgroup gr Z) := ((hTZ.le_QB_iff Hs hRZ).mp hRQT)
  have hTR : T ≠ conjSubgroup gr Z := fun e => by
    have : r ∈ T ⊓ Q := ⟨e ▸ hrR, hrQ⟩
    rw [hTQ, Subgroup.mem_bot] at this
    exact hr1 this
  have htR : t ∉ conjSubgroup gr Z := fun htR =>
    hTR (IsZConjugate.eq_of_mem Hs hTZ hRZ ht1 hT.mem htR)
  have hQRg : QB (conjSubgroup gr Z) = conjSubgroup gr Q := QB_conj_eq Hs gr
  have hNRg : Subgroup.normalizer ((conjSubgroup gr Z : Subgroup G) : Set G) =
      conjSubgroup gr M := normalizer_conj_eq Hs gr
  have hTC : T ≤ Cv v := by
    have hsR : StrothHyp (conjSubgroup gr M) (conjSubgroup gr Q) (conjSubgroup gr Z) := Hs.conj gr
    obtain ⟨g', hg'⟩ := hTZ
    have hTg : ∃ g'' : G, T = conjSubgroup g'' (conjSubgroup gr Z) := by
      refine ⟨g' * gr⁻¹, ?_⟩
      rw [hg', ← conjSubgroup_mul]
      simp [mul_assoc]
    have hctx : Ctx (conjSubgroup gr M) (conjSubgroup gr Q) (conjSubgroup gr Z) T :=
      ⟨hsR, hTg, hQRg ▸ hTQR, hTR⟩
    exact le_Cv_of_fixed_mem hctx (hNRg ▸ hvNR) (fun a ha => by
        have := mem_Cv.mp (hRC ha)
        rw [← this]
        group) hvNT hT.mem htR (by rw [← (mem_Cv.mp htC)]; group)
  have hQRc : QB (conjSubgroup gr Z) = conjSubgroup c Q := by
    rw [hRc]
    exact QB_conj_eq Hs c
  have ht'Q : c⁻¹ * t * c ∈ Q := by
    have h1 : t ∈ QB (conjSubgroup gr Z) := hTQR hT.mem
    rw [hQRc, mem_conjSubgroup] at h1
    exact h1
  have ht'C : c⁻¹ * t * c ∈ Cv v :=
    (Cv v).mul_mem ((Cv v).mul_mem ((Cv v).inv_mem hc) htC) hc
  have ht'conj : IsConj z (c⁻¹ * t * c) := ht.trans (isConj_iff.mpr ⟨c⁻¹, by group⟩)
  obtain ⟨c', hc', ht'c', -⟩ := hS5 _ ht'conj ⟨ht'Q, ht'C⟩
  have htmem : t ∈ conjSubgroup (c * c') Z := by
    rw [mem_conjSubgroup]
    rw [mem_conjSubgroup] at ht'c'
    have e : (c * c')⁻¹ * t * (c * c') = c'⁻¹ * (c⁻¹ * t * c) * c' := by group
    rw [e]
    exact ht'c'
  have hTcc : T = conjSubgroup (c * c') Z :=
    IsZConjugate.eq_of_mem Hs hTZ ⟨c * c', rfl⟩ ht1 hT.mem htmem
  have hTZC : T ∈ ZConjBy (Cv v) Z := ⟨c * c', (Cv v).mul_mem hc hc', hTcc⟩
  have hlink : LinkV v (conjSubgroup gr Z) T := le_inf hTQR hTC
  exact Relation.EqvGen.trans _ _ _ hRblock (Relation.EqvGen.rel _ _ ⟨hRZC, hTZC, hlink⟩)

end Lemma4A2

section FusionCore

variable [Finite G] {M Q Z B : Subgroup G} {z v : G}

private theorem conj_mem_BlockOf_of_le_Qv (Hs : StrothHyp M Q Z) {c : G} (hc : c ∈ Cv v)
    (hcQ : conjSubgroup c Z ≤ Qv Q v) : conjSubgroup c Z ∈ BlockOf (Cv v) Z v := by
  refine Relation.EqvGen.rel _ _ ⟨ZConjBy.self _, ⟨c, hc, rfl⟩, ?_⟩
  show conjSubgroup c Z ≤ QB Z ⊓ Cv v
  rw [Hs.QB_Z]
  exact hcQ

theorem fusionCore_world_of_root (h : E3L45World M Q Z B z v)
    (h212 : ∀ t : G, t ∈ M → t ∉ Q → IsConj z t → ∀ X : Subgroup G, IsZConjugate Z X → t ∈ X →
      (Q ⊓ QB X) ⊔ Z = ⁅Q, Subgroup.zpowers t⁆ ⊔ Z)
    (hS5 : ∀ t : G, IsConj z t → t ∈ Qv Q v →
      ∃ c ∈ Cv v, t ∈ conjSubgroup c Z ∧ conjSubgroup c Z ≤ Qv Q v)
    (hRP : ∀ t : G, IsConj z t → t ∈ Mv M v → t ∉ Q →
      ∃ s : G, IsConj z s ∧ s ∈ Qv Q v ∧ s ∉ Z ∧ s ∈ ⁅Q, Subgroup.zpowers t⁆ ⊔ Z) :
    ∀ t : G, IsConj z t → t ∈ Mv M v → ∃ A ∈ BlockOf (Cv v) Z v, t ∈ A := by
  have Hs := h.hStroth
  intro t ht htM
  by_cases htQ : t ∈ Q
  · obtain ⟨c, hc, htc, hcQ⟩ := hS5 t ht ⟨htQ, htM.2⟩
    exact ⟨conjSubgroup c Z, conj_mem_BlockOf_of_le_Qv Hs hc hcQ, htc⟩
  · obtain ⟨T, hT⟩ := exists_sit_of_isConj Hs h.hz ht htM.1 htQ
    have h212T : (Q ⊓ QB T) ⊔ Z = ⁅Q, Subgroup.zpowers t⁆ ⊔ Z :=
      h212 t htM.1 htQ ht T hT.conj hT.mem
    exact ⟨T, sit_mem_BlockOf_of_rootPoint Hs h.hz h.v_mem_H0 h.hv.2.1 hS5 hT ht htM.2 h212T
      (hRP t ht htM htQ), hT.mem⟩

theorem fusionCore_of_pieces_world (h212 : Smith212Statement) (h : E3L45World M Q Z B z v)
    (hS5 : ∀ t : G, IsConj z t → t ∈ Qv Q v →
      ∃ c ∈ Cv v, t ∈ conjSubgroup c Z ∧ conjSubgroup c Z ≤ Qv Q v)
    (hRP : ∀ t : G, IsConj z t → t ∈ Mv M v → t ∉ Q →
      ∃ s : G, IsConj z s ∧ s ∈ Qv Q v ∧ s ∉ Z ∧ s ∈ ⁅Q, Subgroup.zpowers t⁆ ⊔ Z) :
    ∀ t : G, IsConj z t → t ∈ Mv M v → ∃ A ∈ BlockOf (Cv v) Z v, t ∈ A :=
  fusionCore_world_of_root h
    (fun t htM htQ ht X hX htX =>
      (h212 G M Q Z B h.below h.rem z h.hz h.hz1 t htM htQ ht).2.2.1 X hX htX) hS5 hRP

end FusionCore

@[expose] def E5S5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (z v : G), E3L45World M Q Z B z v →
    InCaseE5 M Q Z B → ∀ t : G, IsConj z t → t ∈ Qv Q v →
      ∃ c ∈ Cv v, t ∈ conjSubgroup c Z ∧ conjSubgroup c Z ≤ Qv Q v

@[expose] def E5RootPointStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (z v : G), E3L45World M Q Z B z v →
    InCaseE5 M Q Z B → ∀ t : G, IsConj z t → t ∈ Mv M v → t ∉ Q →
      ∃ s : G, IsConj z s ∧ s ∈ Qv Q v ∧ s ∉ Z ∧ s ∈ ⁅Q, Subgroup.zpowers t⁆ ⊔ Z

@[expose] def Smith212E3LRootStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → InCaseE3L M Q Z B → ∀ z ∈ Z, z ≠ 1 → ∀ x : G, x ∈ M → x ∉ Q → IsConj z x →
      ∀ X : Subgroup G, IsZConjugate Z X → x ∈ X →
        (Q ⊓ QB X) ⊔ Z = ⁅Q, Subgroup.zpowers x⁆ ⊔ Z

theorem e5FusionCore_of_pieces (h212 : Smith212Statement)
    (hS5 : E5S5Statement) (hRP : E5RootPointStatement) : E5FusionCoreStatement :=
  fun G _ _ M Q Z B z v h hc =>
    fusionCore_of_pieces_world h212 h (hS5 G M Q Z B z v h hc) (hRP G M Q Z B z v h hc)

end CFSG.RankThree.GF2n.Smith81
