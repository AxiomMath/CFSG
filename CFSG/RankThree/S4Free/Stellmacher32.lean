module

public import CFSG.RankThree.S4Free.Stellmacher31
import CFSG.Quasithin.Background.AutOnElemAb
import CFSG.Quasithin.Background.AutOnIndex

public section

namespace CFSG.RankThree.S4Free.Stell

open CFSG.Quasithin CFSG.Open Subgroup

universe u

section ThompsonJ

variable {G G' : Type*} [Group G] [Group G']

theorem isElemAbelian_of_map {f : G →* G'} (hf : Function.Injective f) {A : Subgroup G}
    (h : IsElemAbelian 2 (A.map f)) : IsElemAbelian 2 A := by
  refine isElemAbelian_of_forall (fun a ha b hb => hf ?_) (fun a ha => hf ?_)
  · rw [map_mul, map_mul]
    exact isElemAbelian_comm h ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  · rw [map_pow, map_one]
    exact h.2 _ ⟨a, ha, rfl⟩

theorem isMaxElemAbelian_map_iff {f : G →* G'} (hf : Function.Injective f) {H A : Subgroup G} :
    IsMaxElemAbelian (H.map f) (A.map f) ↔ IsMaxElemAbelian H A := by
  constructor
  · rintro ⟨hAH, hA, hmax⟩
    refine ⟨(Subgroup.map_le_map_iff_of_injective hf).mp hAH, isElemAbelian_of_map hf hA,
      fun B hBH hB => ?_⟩
    have := hmax (B.map f) (Subgroup.map_mono hBH) (CFSG.RankThree.S4Free.isElemAbelian_map hB f)
    rwa [Subgroup.card_map_of_injective hf, Subgroup.card_map_of_injective hf] at this
  · rintro ⟨hAH, hA, hmax⟩
    refine ⟨Subgroup.map_mono hAH, CFSG.RankThree.S4Free.isElemAbelian_map hA f,
      fun B' hB'H hB' => ?_⟩
    have hB'r : B' ≤ f.range := hB'H.trans (Subgroup.map_le_range _ _)
    have hB'eq : (B'.comap f).map f = B' := by
      rw [Subgroup.map_comap_eq, inf_eq_right.mpr hB'r]
    have hcomapH : B'.comap f ≤ H := by
      intro b hb
      obtain ⟨h, hh, hfh⟩ := hB'H hb
      rwa [hf hfh] at hh
    have h1 := hmax (B'.comap f) hcomapH (isElemAbelian_of_map hf (by rw [hB'eq]; exact hB'))
    rw [← hB'eq, Subgroup.card_map_of_injective hf, Subgroup.card_map_of_injective hf]
    exact h1

theorem thompsonJ_map_of_injective {f : G →* G'} (hf : Function.Injective f) (H : Subgroup G) :
    thompsonJ (H.map f) = (thompsonJ H).map f := by
  apply le_antisymm
  · refine iSup₂_le fun A' hA' => ?_
    have hA'r : A' ≤ f.range := hA'.1.trans (Subgroup.map_le_range _ _)
    have hA'eq : (A'.comap f).map f = A' := by
      rw [Subgroup.map_comap_eq, inf_eq_right.mpr hA'r]
    rw [← hA'eq] at hA' ⊢
    exact Subgroup.map_mono (le_iSup₂_of_le (A'.comap f) ((isMaxElemAbelian_map_iff hf).mp hA')
      le_rfl)
  · rw [thompsonJ, Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hA => le_iSup₂_of_le (A.map f) ((isMaxElemAbelian_map_iff hf).mpr hA) le_rfl

variable [Finite G]

theorem exists_isMaxElemAbelian (H : Subgroup G) : ∃ A, IsMaxElemAbelian H A := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨A, hA, hmax⟩ := Set.exists_max_image {B : Subgroup G | B ≤ H ∧ IsElemAbelian 2 B}
    (fun B => Nat.card B) (Set.toFinite _) ⟨⊥, bot_le, ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩,
      fun x hx => by rw [Subgroup.mem_bot.1 hx, one_pow]⟩⟩
  exact ⟨A, hA.1, hA.2, fun B hBH hB => hmax B ⟨hBH, hB⟩⟩

theorem thompsonJ_eq_of_le {Q T : Subgroup G} (hQT : Q ≤ T) (hJ : thompsonJ T ≤ Q) :
    thompsonJ Q = thompsonJ T := by
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T
  have hA₀Q : A₀ ≤ Q := (le_iSup₂_of_le A₀ hA₀ le_rfl).trans hJ
  have key : ∀ A, IsMaxElemAbelian Q A ↔ IsMaxElemAbelian T A := by
    intro A
    constructor
    · rintro ⟨hAQ, hA, hmax⟩
      exact ⟨hAQ.trans hQT, hA, fun B hBT hB =>
        (hA₀.2.2 B hBT hB).trans (hmax A₀ hA₀Q hA₀.2.1)⟩
    · intro hA
      exact ⟨(le_iSup₂_of_le A hA le_rfl).trans hJ, hA.2.1, fun B hBQ hB =>
        hA.2.2 B (hBQ.trans hQT) hB⟩
  apply le_antisymm
  · exact iSup₂_le fun A hA => le_iSup₂_of_le A ((key A).mp hA) le_rfl
  · exact iSup₂_le fun A hA => le_iSup₂_of_le A ((key A).mpr hA) le_rfl

theorem normal_thompsonJ {Q : Subgroup G} (hQ : Q.Normal) : (thompsonJ Q).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hmap : (thompsonJ Q).map (MulAut.conj g).toMonoidHom ≤ thompsonJ Q := by
    have hQg : Q.map (MulAut.conj g).toMonoidHom = Q := by
      ext x
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact hQ.conj_mem q hq g
      · intro hx
        refine ⟨g⁻¹ * x * g⁻¹⁻¹, hQ.conj_mem x hx g⁻¹, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    rw [← thompsonJ_map_of_injective (MulAut.conj g).injective, hQg]
  exact hmap ⟨n, hn, rfl⟩

end ThompsonJ

section Offenders

variable {G : Type*} [Group G]

@[expose] def mulProdHom {Y C : Subgroup G} (hC : ∀ c ∈ C, ∀ y ∈ Y, y * c = c * y) :
    (↥Y × ↥C) →* G where
  toFun p := (p.1 : G) * (p.2 : G)
  map_one' := by simp
  map_mul' p q := by
    show ((p.1 * q.1 : ↥Y) : G) * ((p.2 * q.2 : ↥C) : G) =
      ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
    simp only [Subgroup.coe_mul]
    calc (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G))
        = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by simp only [mul_assoc]
      _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by
          rw [hC (p.2 : G) p.2.2 (q.1 : G) q.1.2]
      _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by simp only [mul_assoc]

theorem map_conj_centralizer (T : Subgroup G) (x : G) :
    (centralizer (T : Set G)).map (MulAut.conj x).toMonoidHom =
      centralizer ((T.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  ext g
  rw [mem_map_conj, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩ _ ⟨t, ht, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := Subgroup.mem_centralizer_iff.mp hc t ht
    calc x * t * x⁻¹ * (x * c * x⁻¹) = x * (t * c) * x⁻¹ := by group
      _ = x * (c * t) * x⁻¹ := by rw [this]
      _ = x * c * x⁻¹ * (x * t * x⁻¹) := by group
  · intro h
    refine ⟨x⁻¹ * g * x, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_, by group⟩
    have := h (x * t * x⁻¹) ⟨t, ht, rfl⟩
    calc t * (x⁻¹ * g * x) = x⁻¹ * ((x * t * x⁻¹) * g) * x := by group
      _ = x⁻¹ * (g * (x * t * x⁻¹)) * x := by rw [this]
      _ = x⁻¹ * g * x * t := by group

variable [Finite G]

theorem relIndex_le_of_isMaxElemAbelian {P Y A : Subgroup G} (hA : IsMaxElemAbelian P A)
    (hYP : Y ≤ P) (hY : IsElemAbelian 2 Y) :
    (Y ⊓ centralizer (A : Set G)).relIndex Y ≤ (A ⊓ centralizer (Y : Set G)).relIndex A := by
  set C := A ⊓ centralizer (Y : Set G) with hCdef
  set K := Y ⊓ centralizer (A : Set G) with hKdef
  have hCA : C ≤ A := inf_le_left
  have hC : ∀ c ∈ C, ∀ y ∈ Y, y * c = c * y := fun c hc y hy =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 y hy
  set f := mulProdHom hC with hf
  have hcommD : ∀ p q : ↥Y × ↥C, p * q = q * p := by
    rintro ⟨y, c⟩ ⟨y', c'⟩
    ext
    · exact isElemAbelian_comm hY y.2 y'.2
    · exact isElemAbelian_comm hA.2.1 (hCA c.2) (hCA c'.2)
  have hrangeEl : IsElemAbelian 2 f.range := by
    refine isElemAbelian_of_forall ?_ ?_
    · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
      rw [← map_mul, ← map_mul, hcommD]
    · rintro _ ⟨p, rfl⟩
      have hp2 : p ^ 2 = 1 := by
        ext
        · exact hY.2 _ p.1.2
        · exact hA.2.1.2 _ (hCA p.2.2)
      rw [← map_pow, hp2, map_one]
  have hrangeP : f.range ≤ P := by
    rintro _ ⟨p, rfl⟩
    exact P.mul_mem (hYP p.1.2) (hA.1 (hCA p.2.2))
  have hrange : Nat.card f.range ≤ Nat.card A := hA.2.2 _ hrangeP hrangeEl
  have hker : Nat.card f.ker ≤ Nat.card K := by
    refine Nat.card_le_card_of_injective (fun p => (⟨p.1.1.1, ?_⟩ : K)) ?_
    · have hp : (p.1.1 : G) * (p.1.2 : G) = 1 := p.2
      have h1 : (p.1.1 : G) = (p.1.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left hp
      refine Subgroup.mem_inf.mpr ⟨p.1.1.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      rw [h1]
      exact isElemAbelian_comm hA.2.1 ha (A.inv_mem (hCA p.1.2.2))
    · intro p q hpq
      have h1 : (p.1.1 : G) = q.1.1 := congrArg (fun z : K => (z : G)) hpq
      have hp : (p.1.1 : G) * (p.1.2 : G) = 1 := p.2
      have hq : (q.1.1 : G) * (q.1.2 : G) = 1 := q.2
      have h2 : (p.1.2 : G) = q.1.2 := by
        rw [eq_inv_of_mul_eq_one_right hp, eq_inv_of_mul_eq_one_right hq, h1]
      exact Subtype.ext (Prod.ext (Subtype.ext h1) (Subtype.ext h2))
  have hkr := Subgroup.card_ker_mul_card_range f
  rw [Nat.card_prod] at hkr
  have hK := Subgroup.relIndex_mul_card K Y
  rw [inf_eq_left.mpr inf_le_left] at hK
  have hB := Subgroup.relIndex_mul_card C A
  rw [inf_eq_left.mpr hCA] at hB
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have key : K.relIndex Y * (Nat.card K * Nat.card C) ≤
      C.relIndex A * (Nat.card K * Nat.card C) := by
    calc K.relIndex Y * (Nat.card K * Nat.card C) = Nat.card Y * Nat.card C := by
          rw [← hK]; ring
      _ = Nat.card f.ker * Nat.card f.range := hkr.symm
      _ ≤ Nat.card K * Nat.card A := Nat.mul_le_mul hker hrange
      _ = C.relIndex A * (Nat.card K * Nat.card C) := by rw [← hB]; ring
  exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos hKpos hCpos)

section

open scoped IsMulCommutative

theorem ale_one_autOn_of_relIndex_le {P A B : Subgroup G} [IsMulCommutative A]
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hPA : P ≤ normalizer (A : Set G)) (hBP : B ≤ P)
    (hB : IsElemAbelian 2 B) (hBA : ¬ B ≤ centralizer (A : Set G))
    (hle : (A ⊓ centralizer (B : Set G)).relIndex A ≤
      (B ⊓ centralizer (A : Set G)).relIndex B) : ALe (autOn P A) ⊤ 1 := by
  have hBN : B ≤ normalizer (A : Set G) := hBP.trans hPA
  have hA2' : ∀ a : A, a ^ 2 = 1 := fun a => Subtype.ext (hA2 a a.2)
  have hel : IsElemAbelian2 (autOn B A) := AutOn.isElemAbelian2_autOn hB
  have hfix : fixV (autOn B A) = (centralizer (B : Set G)).subgroupOf A :=
    AutOn.fixV_autOn_eq hBN
  refine ⟨autOn B A, ⟨AutOn.autOn_mono hBP, fun hle' => hBA ?_, IsElemAbelian2.elemAbOn hel ⊤⟩,
    ?_⟩
  · intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : (⟨a, ha⟩ : A) ∈ fixV (autOn B A) := hle' (Subgroup.mem_top _)
    rw [hfix, Subgroup.mem_subgroupOf] at ha'
    exact ((Subgroup.mem_centralizer_iff.mp ha') b hb).symm
  · rw [one_mul, dimOn_top, codimOn_top]
    have hidx : (fixV (autOn B A)).index = (A ⊓ centralizer (B : Set G)).relIndex A := by
      rw [hfix, Subgroup.inf_relIndex_left]
      rfl
    have hcard : Nat.card (autOn B A) = (B ⊓ centralizer (A : Set G)).relIndex B :=
      AutOn.card_autOn_eq_relIndex hBN
    rw [← hidx, ← hcard, B1.index_eq_two_pow hA2', B1.card_elemAbelian hel] at hle
    exact_mod_cast (Nat.pow_le_pow_iff_right (by norm_num)).mp hle

theorem ale_one_autOn_of_isMaxElemAbelian_le {P A Y : Subgroup G} [IsMulCommutative Y]
    (hA : IsMaxElemAbelian P A) (hYP : Y ≤ P) (hY : IsElemAbelian 2 Y)
    (hPY : P ≤ normalizer (Y : Set G)) (hAY : ¬ A ≤ centralizer (Y : Set G)) :
    ALe (autOn P Y) ⊤ 1 :=
  ale_one_autOn_of_relIndex_le hY.2 hPY hA.1 hA.2.1 hAY
    (relIndex_le_of_isMaxElemAbelian hA hYP hY)

theorem ale_one_autOn_of_conj {P A : Subgroup G} [IsMulCommutative A] (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hPA : P ≤ normalizer (A : Set G)) {x : G} (hx : A.map (MulAut.conj x).toMonoidHom ≤ P)
    (hx' : A.map (MulAut.conj x⁻¹).toMonoidHom ≤ P)
    (hcomm : ¬ A.map (MulAut.conj x).toMonoidHom ≤ centralizer (A : Set G)) :
    ALe (autOn P A) ⊤ 1 := by
  set c := (MulAut.conj x).toMonoidHom with hc
  have hinj : Function.Injective c := (MulAut.conj x).injective
  set B := A.map c with hB
  set B' := A.map (MulAut.conj x⁻¹).toMonoidHom with hB'
  have hAel : IsElemAbelian 2 A := ⟨inferInstance, hA2⟩
  have hBel : IsElemAbelian 2 B := CFSG.RankThree.S4Free.isElemAbelian_map hAel c
  have hB'el : IsElemAbelian 2 B' := CFSG.RankThree.S4Free.isElemAbelian_map hAel _
  have hB'c : B'.map c = A := by
    rw [hB', Subgroup.map_map]
    have : c.comp (MulAut.conj x⁻¹).toMonoidHom = MonoidHom.id G := by
      ext g
      simp only [hc, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [this, Subgroup.map_id]
  by_cases hle : (A ⊓ centralizer (B : Set G)).relIndex A ≤
      (B ⊓ centralizer (A : Set G)).relIndex B
  · exact ale_one_autOn_of_relIndex_le hA2 hPA hx hBel hcomm hle
  · push Not at hle
    have e1 : (A ⊓ centralizer (B' : Set G)).relIndex A =
        (B ⊓ centralizer (A : Set G)).relIndex B := by
      rw [← Subgroup.relIndex_map_map_of_injective _ _ hinj, Subgroup.map_inf_eq _ _ _ hinj,
        map_conj_centralizer, ← hc, hB'c]
    have e2 : (B' ⊓ centralizer (A : Set G)).relIndex B' =
        (A ⊓ centralizer (B : Set G)).relIndex A := by
      rw [← Subgroup.relIndex_map_map_of_injective _ _ hinj, Subgroup.map_inf_eq _ _ _ hinj,
        map_conj_centralizer, ← hc, hB'c]
    have hB'A : ¬ B' ≤ centralizer (A : Set G) := by
      intro h
      apply hcomm
      have h1 := Subgroup.map_mono (f := c) h
      rw [hB'c, hc, map_conj_centralizer, ← hc] at h1
      exact Subgroup.le_centralizer_iff.mp h1
    exact ale_one_autOn_of_relIndex_le hA2 hPA hx' hB'el hB'A (by rw [e1, e2]; exact hle.le)

end

end Offenders

theorem _root_.CFSG.RankThree.S4Free.F2Host.not_map_thompsonJ_le_oTwo {𝒦 : HostClass}
    {S : Type*} [Group S] {X : Type*}
    [Group X] {ι : S →* X} (h : F2Host 𝒦 ι) :
    ¬ (thompsonJ (⊤ : Subgroup S)).map ι ≤ oTwo X := by
  have := h.admissible.finite
  intro hle
  apply h.not_normal_thompsonJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := h.admissible.sylow
  have hOT : oTwo X ≤ ι.range := hP ▸ (isPGroup_oTwo X).le_sylow_of_normal P
  rw [← thompsonJ_map_of_injective h.admissible.injective, ← MonoidHom.range_eq_map] at hle ⊢
  rw [← thompsonJ_eq_of_le hOT hle]
  exact normal_thompsonJ inferInstance

section ThreeTwo

open scoped IsMulCommutative

variable {𝒦 : HostClass} {S : Type u} [Group S]

theorem _root_.CFSG.RankThree.S4Free.F2Host.pResidual_le_centralizer_or_not_le_oTwo
    (h24 : Hyp29.{u} 𝒦) [Finite S]
    {U : Subgroup S} (hU : AGtOne U) (hUel : IsElemAbelian 2 U) {X : Type u} [Group X]
    {ι : S →* X} (hι : F2Host 𝒦 ι) :
    pResidual 2 X ≤ centralizer ((U.map ι : Subgroup X) : Set X) ∨ ¬ U.map ι ≤ oTwo X := by
  have := hι.admissible.finite
  have hinj := hι.admissible.injective
  by_contra hcon
  push Not at hcon
  obtain ⟨hres, hUO⟩ := hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hι.admissible.sylow
  have hOT : oTwo X ≤ ι.range := hP ▸ (isPGroup_oTwo X).le_sylow_of_normal P
  have hS2 : IsPGroup 2 ι.range := hP ▸ P.isPGroup'
  have hSi : ¬ 2 ∣ ι.range.relIndex ⊤ := by
    rw [Subgroup.relIndex_top_right, ← hP]
    exact P.not_dvd_index
  haveI : IsMulCommutative U := hUel.1
  have hAel : IsElemAbelian 2 (U.map ι) := CFSG.RankThree.S4Free.isElemAbelian_map hUel ι
  haveI : IsMulCommutative (U.map ι) := hAel.1
  have hAN : ι.range ≤ normalizer ((U.map ι : Subgroup X) : Set X) :=
    range_le_normalizer_map ι hU.1
  have hAgt : AGt (autOn ι.range (U.map ι)) ⊤ 1 := by
    have hnormS : (⊤ : Subgroup S) ≤ normalizer (U : Set S) :=
      fun x _ => by rw [normalizer_eq_top_iff.mpr hU.1]; exact Subgroup.mem_top x
    have hN : (⊤ : Subgroup S).map ι ≤ normalizer ((U.map ι : Subgroup X) : Set X) := by
      rw [← MonoidHom.range_eq_map]
      exact hAN
    have h := (agt_autOn_map_iff (f := ι) (P := ⊤) (U := U) (Y := U.map ι) hinj hnormS le_rfl
      hN).mpr hU.2
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h
  by_cases hcomm : ∀ x : X, U.map ι ≤
      centralizer (((U.map ι).map (MulAut.conj x).toMonoidHom : Subgroup X) : Set X)
  ·
    set Y := normalClosure ((U.map ι : Subgroup X) : Set X) with hY
    have hYel : IsElemAbelian 2 Y := by
      rw [hY, Subgroup.normalClosure]
      refine isElemAbelian_closure_of_commute ?_ ?_
      · intro a ha b hb
        obtain ⟨a', ha', hca⟩ := Group.mem_conjugatesOfSet_iff.mp ha
        obtain ⟨b', hb', hcb⟩ := Group.mem_conjugatesOfSet_iff.mp hb
        obtain ⟨g, rfl⟩ := isConj_iff.mp hca
        obtain ⟨k, rfl⟩ := isConj_iff.mp hcb
        have h1 := Subgroup.mem_centralizer_iff.mp (hcomm (g⁻¹ * k) ha')
          ((g⁻¹ * k) * b' * (g⁻¹ * k)⁻¹) ⟨b', hb', rfl⟩
        calc g * a' * g⁻¹ * (k * b' * k⁻¹)
            = g * (a' * ((g⁻¹ * k) * b' * (g⁻¹ * k)⁻¹)) * g⁻¹ := by group
          _ = g * (((g⁻¹ * k) * b' * (g⁻¹ * k)⁻¹) * a') * g⁻¹ := by rw [h1]
          _ = k * b' * k⁻¹ * (g * a' * g⁻¹) := by group
      · intro a ha
        obtain ⟨a', ha', hca⟩ := Group.mem_conjugatesOfSet_iff.mp ha
        obtain ⟨g, rfl⟩ := isConj_iff.mp hca
        rw [conj_pow, hAel.2 a' ha', mul_one, mul_inv_cancel]
    haveI : IsMulCommutative Y := hYel.1
    have hYO : Y ≤ oTwo X := normalClosure_le_normal hUO
    have hYn : Y.Normal := normalClosure_normal
    have hYN : (⊤ : Subgroup X) ≤ normalizer (Y : Set X) := fun x _ => by
      rw [normalizer_eq_top_iff.mpr hYn]
      exact Subgroup.mem_top x
    have hYgt : AGt (autOn ι.range Y) ⊤ 1 := by
      refine agt_autOn_of_agt h24 (H := ⊤) (Z := U.map ι) hYel.2
        (HostClass.Holds.of_mulEquiv Subgroup.topEquiv.symm hι.holds)
        (IsSym3Free.of_mulEquiv Subgroup.topEquiv.symm hι.admissible.isSym3Free) hYN le_top
        hS2 hSi le_normalClosure hAN ?_ hAgt
      intro W hW
      rw [hY, Subgroup.normalClosure, Subgroup.closure_le]
      intro x hx
      obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨c, rfl⟩ := isConj_iff.mp hax
      exact hW c (Subgroup.mem_top c) ⟨a, ha, rfl⟩
    have hJ : (thompsonJ (⊤ : Subgroup S)).map ι ≤ centralizer (Y : Set X) := by
      rw [← thompsonJ_map_of_injective hinj, ← MonoidHom.range_eq_map]
      refine iSup₂_le fun A hA => ?_
      by_contra hnot
      exact not_ale_iff.mpr hYgt (ale_one_autOn_of_isMaxElemAbelian_le hA (hYO.trans hOT) hYel
        (le_top.trans hYN) hnot)
    rcases hι.condM _ (inferInstance : (centralizer (Y : Set X)).Normal) with h | h
    · exact hι.not_map_thompsonJ_le_oTwo ((le_inf (Subgroup.map_le_range _ _) hJ).trans h)
    · exact hres (h.trans (Subgroup.centralizer_le (le_normalClosure : U.map ι ≤ Y)))
  · push Not at hcomm
    obtain ⟨x, hx⟩ := hcomm
    have hconj : ∀ g : X, (U.map ι).map (MulAut.conj g).toMonoidHom ≤ ι.range := by
      rintro g _ ⟨a, ha, rfl⟩
      exact hOT ((inferInstance : (oTwo X).Normal).conj_mem _ (hUO ha) g)
    refine not_ale_iff.mpr hAgt (ale_one_autOn_of_conj hAel.2 hAN (hconj x) (hconj x⁻¹) ?_)
    intro h
    exact hx (Subgroup.le_centralizer_iff.mp h)

theorem _root_.CFSG.RankThree.S4Free.F2Host.normal_map_iff_pResidual_le_centralizer
    (h24 : Hyp29.{u} 𝒦) [Finite S] {U : Subgroup S} (hU : AGtOne U) (hUel : IsElemAbelian 2 U)
    {X : Type u} [Group X] {ι : S →* X} (hι : F2Host 𝒦 ι) :
    (U.map ι).Normal ↔ pResidual 2 X ≤ centralizer ((U.map ι : Subgroup X) : Set X) := by
  have := hι.admissible.finite
  constructor
  · intro hn
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : IsPGroup 2 (U.map ι) :=
      IsPGroup.map (fun u => ⟨1, Subtype.ext (by simpa using hUel.2 u u.2)⟩) ι
    have hle : U.map ι ≤ oTwo X := le_oTwo h2
    exact (hι.pResidual_le_centralizer_or_not_le_oTwo h24 hU hUel).resolve_right
      (not_not.mpr hle)
  · intro h
    refine (normal_map_iff_pResidual_le_normalizer hι.admissible.sylow hU.1).mpr
      (h.trans fun g hg => ?_)
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      rw [← Subgroup.mem_centralizer_iff.mp hg t ht, mul_inv_cancel_right]
      exact ht
    · intro ht
      have := Subgroup.mem_centralizer_iff.mp hg
      have hgt : g * t * g⁻¹ = t := by
        have h1 : ∀ s ∈ (U.map ι : Subgroup X), s * g = g * s := this
        have h2 := h1 _ ht
        calc g * t * g⁻¹ = g⁻¹ * (g * (g * t * g⁻¹)) * g⁻¹ * g⁻¹⁻¹ * g⁻¹ * g := by group
          _ = g⁻¹ * ((g * t * g⁻¹) * g) * g⁻¹ * g⁻¹⁻¹ * g⁻¹ * g := by rw [h2]
          _ = t := by group
      rw [hgt] at ht
      exact ht

theorem stellW_normal_of_f2_card_le [Finite S] {n : ℕ}
    (hF2 : ∀ (Y : Type u) [Group Y] (κ : S →* Y), F2Host 𝒦 κ → Nat.card Y ≤ n →
      ((stellW 𝒦 S).map κ).Normal)
    {X : Type u} [Group X] {ι : S →* X} (hι : IsAdmissibleHost ι) (hX : 𝒦.Holds X)
    (hXn : Nat.card X ≤ n) : ((stellW 𝒦 S).map ι).Normal := by
  have := hι.finite
  refine normal_of_forall_condM hι.sylow _ fun K hK hM => ?_
  refine le_normalizer_of_normal_codRestrict hι.injective hK ?_
  rcases f1Host_or_f2Host (hι.restrict hK) (hX.subgroup K) hM with h | h
  · exact stellW_normal h
  · exact hF2 K _ h ((Subgroup.card_le_card_group K).trans hXn)

theorem _root_.CFSG.RankThree.S4Free.F2Host.minimal_counterexample (h24 : Hyp29.{u} 𝒦)
    [Finite S] {X : Type u} [Group X] {ι : S →* X} (hι : F2Host 𝒦 ι)
    (hmin : ∀ (Y : Type u) [Group Y] (κ : S →* Y), F2Host 𝒦 κ → Nat.card Y < Nat.card X →
      ((stellW 𝒦 S).map κ).Normal)
    (hW : ¬ ((stellW 𝒦 S).map ι).Normal) :
    (∀ K : Subgroup X, ι.range ≤ K → K ≠ ⊤ →
        K ≤ normalizer (((stellW 𝒦 S).map ι : Subgroup X) : Set X)) ∧
      normalizer (((stellW 𝒦 S).map ι : Subgroup X) : Set X) ≠ ⊤ ∧
      ¬ (stellW 𝒦 S).map ι ≤ oTwo X := by
  have := hι.admissible.finite
  refine ⟨fun K hK hKtop => ?_, fun htop => hW (normalizer_eq_top_iff.mp htop), fun hle => ?_⟩
  · have hcard : Nat.card K < Nat.card X :=
      lt_of_le_of_ne (Subgroup.card_le_card_group K) fun h =>
        hKtop ((Subgroup.card_eq_iff_eq_top K).1 h)
    refine le_normalizer_of_normal_codRestrict hι.admissible.injective hK ?_
    exact stellW_normal_of_f2_card_le (n := Nat.card X - 1)
      (fun Y _ κ hκ hY => hmin Y κ hκ (by omega)) (hι.admissible.restrict hK)
      (hι.holds.subgroup K) (by omega)
  · have hU := agtOne_stellW (𝒦 := 𝒦) (S := S) h24
    have hel := isElemAbelian_stellW (𝒦 := 𝒦) (S := S)
    exact hW ((hι.normal_map_iff_pResidual_le_centralizer h24 hU hel).mpr
      ((hι.pResidual_le_centralizer_or_not_le_oTwo h24 hU hel).resolve_right (not_not.mpr hle)))

theorem _root_.CFSG.RankThree.S4Free.F2Host.map_mulEquiv {S : Type*} [Group S] {X Y : Type*}
    [Group X] [Group Y] {ι : S →* X} (h : F2Host 𝒦 ι) (e : X ≃* Y) :
    F2Host 𝒦 (e.toMonoidHom.comp ι) := by
  have := h.admissible.finite
  have hO : (oTwo X).map e.toMonoidHom = oTwo Y := oTwo_map_mulEquiv e
  refine ⟨h.admissible.map_mulEquiv e, h.holds.of_mulEquiv e, fun N hN => ?_, fun hn => ?_⟩
  · have hN' : (N.comap e.toMonoidHom).Normal := hN.comap _
    rcases h.condM _ hN' with h1 | h1
    · left
      have := Subgroup.map_mono (f := e.toMonoidHom) h1
      rwa [Subgroup.map_inf _ _ _ e.injective, ← MonoidHom.range_comp,
        Subgroup.map_comap_eq_self_of_surjective e.surjective, hO] at this
    · right
      have := Subgroup.map_mono (f := e.toMonoidHom) h1
      rwa [map_pResidual_mulEquiv, Subgroup.map_comap_eq_self_of_surjective e.surjective] at this
  · apply h.not_normal_thompsonJ
    have h2 := hn.map e.symm.toMonoidHom e.symm.surjective
    rwa [← Subgroup.map_map, Subgroup.map_map (f := e.toMonoidHom), show
      e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X by ext; simp, Subgroup.map_id] at h2

theorem stellW_normal_of_f2_of_type.{v} [Finite S]
    (hF2 : ∀ (Y : Type u) [Group Y] (κ : S →* Y), F2Host 𝒦 κ → ((stellW 𝒦 S).map κ).Normal)
    {X : Type v} [Group X] {ι : S →* X} (h : F2Host 𝒦 ι) : ((stellW 𝒦 S).map ι).Normal := by
  have := h.admissible.finite
  let e : X ≃* Shrink.{u} X := Shrink.mulEquiv.symm
  have h' := hF2 _ _ (h.map_mulEquiv e)
  have h'' := h'.map e.symm.toMonoidHom e.symm.surjective
  rwa [Subgroup.map_map, ← MonoidHom.comp_assoc, show e.symm.toMonoidHom.comp e.toMonoidHom =
    MonoidHom.id X by ext; simp, MonoidHom.id_comp] at h''

end ThreeTwo

end CFSG.RankThree.S4Free.Stell
