module

public import CFSG.Timmesfeld.Transvection.TriangleCoords
public import CFSG.Timmesfeld.Transvection.LineSpan

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

theorem mem_sup_of_commuting {H K : Subgroup G} (h : Commuting H K) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ y ∈ H, ∃ z ∈ K, y * z = x := by
  have hle : H ≤ Subgroup.normalizer (K : Set G) := fun y hy =>
    conjSub_eq_self_iff.1 (conjSub_of_forall_commute fun z hz => h y hy z hz)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right H K hle] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  exact ⟨y, hy, z, hz, rfl⟩

theorem sup_inf_eq_bot [Finite G] (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ)
    (hpts : PointsDetermined Δ) {C₁ C₂ C₃ : Subgroup G} (h₁ : C₁ ∈ Δ) (h₂ : C₂ ∈ Δ)
    (h₃ : C₃ ∈ Δ) (h12 : C₁ ≠ C₂) (h13 : C₁ ≠ C₃) (h23 : C₂ ≠ C₃) (c12 : Commuting C₁ C₂) :
    (C₁ ⊔ C₂) ⊓ C₃ = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  by_contra hx1
  obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup_of_commuting c12 hx.1
  have hx3 := hx.2
  by_cases hy1 : y = 1
  · subst hy1
    rw [one_mul] at hx3 hx1
    exact h23 (hΔ.eq_of_mem_of_mem hiso h₂ h₃ hz hx3 hx1)
  by_cases hz1 : z = 1
  · subst hz1
    rw [mul_one] at hx3 hx1
    exact h13 (hΔ.eq_of_mem_of_mem hiso h₁ h₃ hy hx3 hx1)
  refine h13 (eq_of_commuting_subset hΔ hpts h₃ h₁ fun W hW hW3 => ?_)
  obtain ⟨w, hw, hw1⟩ := hΔ.root.exists_ne_one hW
  have hwy := (commute_mul_iff hΔ hiso hW h₁ h₂ h12 c12 hw hw1 hy hy1 hz hz1).1
    (hW3 _ hx3 w hw).symm
  exact (hΔ.commuting_of_commute hiso hW h₁ hw hw1 hy hy1 hwy.1).symm

theorem card_sup_sup_of_ne [Finite G] (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ)
    (hpts : PointsDetermined Δ) {C₁ C₂ C₃ : Subgroup G} (h₁ : C₁ ∈ Δ) (h₂ : C₂ ∈ Δ)
    (h₃ : C₃ ∈ Δ) (h12 : C₁ ≠ C₂) (h13 : C₁ ≠ C₃) (h23 : C₂ ≠ C₃) (c12 : Commuting C₁ C₂)
    (c13 : Commuting C₁ C₃) (c23 : Commuting C₂ C₃) :
    Nat.card ↥(C₁ ⊔ C₂ ⊔ C₃) = Nat.card C₁ ^ 3 := by
  have h1 := le_antisymm (card_sup_le_of_commuting (c13.sup_left c23))
    (card_mul_card_le_card_sup (sup_inf_eq_bot hΔ hiso hpts h₁ h₂ h₃ h12 h13 h23 c12))
  have h2 := le_antisymm (card_sup_le_of_commuting c12)
    (card_mul_card_le_card_sup (hΔ.inf_eq_bot hiso h₁ h₂ h12))
  rw [h1, h2, hΔ.root.card_eq h₂ h₁, hΔ.root.card_eq h₃ h₁]
  ring

theorem card_sup_sup_le [Finite G] (hΔ : IsTransvectionClass Δ) {C₁ C₂ C₃ : Subgroup G}
    (h₁ : C₁ ∈ Δ) (h₂ : C₂ ∈ Δ) (h₃ : C₃ ∈ Δ) (c12 : Commuting C₁ C₂) (c13 : Commuting C₁ C₃)
    (c23 : Commuting C₂ C₃) : Nat.card ↥(C₁ ⊔ C₂ ⊔ C₃) ≤ Nat.card C₁ ^ 3 := by
  calc Nat.card ↥(C₁ ⊔ C₂ ⊔ C₃) ≤ Nat.card ↥(C₁ ⊔ C₂) * Nat.card C₃ :=
        card_sup_le_of_commuting (c13.sup_left c23)
    _ ≤ Nat.card C₁ * Nat.card C₂ * Nat.card C₃ :=
        Nat.mul_le_mul_right _ (card_sup_le_of_commuting c12)
    _ = Nat.card C₁ ^ 3 := by rw [hΔ.root.card_eq h₂ h₁, hΔ.root.card_eq h₃ h₁]; ring

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G} (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
include S htY

theorem conjSub_le_corrL [Finite G] (hq : 4 ≤ Nat.card A) {n : G} (hn : n ∈ corrN A E t) :
    conjSub A n ≤ corrL A E t := by
  rw [← S.conjSub_corrL_of_mem_corrN (S.fourTerm htY hq) hq hn]
  exact Subgroup.map_mono le_corrL

theorem corrL_eq_iSup [Finite G] (hq : 4 ≤ Nat.card A) :
    corrL A E t = ⨆ n ∈ corrN A E t, conjSub A n := by
  refine le_antisymm (iSup₂_le ?_) (iSup₂_le fun n hn => S.conjSub_le_corrL htY hq hn)
  rintro _ ⟨m, hm, rfl⟩
  exact le_iSup₂_of_le m (corrM_le_corrN hm) le_rfl

theorem commute_of_mem_corrL' [Finite G] (hq : 4 ≤ Nat.card A) {x y : G}
    (hx : x ∈ corrL A E t) (hy : y ∈ corrL A E t) : Commute x y :=
  S.commute_of_mem_corrL (S.fourTerm htY hq) hx hy

theorem commuting_of_le_corrL [Finite G] (hq : 4 ≤ Nat.card A) {C D : Subgroup G}
    (hC : C ≤ corrL A E t) (hD : D ≤ corrL A E t) : Commuting C D :=
  fun _ hx _ hy => S.commute_of_mem_corrL' htY hq (hC hx) (hD hy)

omit htY in
theorem corrL_le_sup : corrL A E t ≤ A ⊔ E ⊔ B := by
  refine iSup₂_le ?_
  rintro _ ⟨m, hm, rfl⟩
  exact conjSub_le (le_sup_left.trans le_sup_left) (S.corrN_le_sup (corrM_le_corrN hm))

theorem sup_conjSub_eq [Finite G] (hq : 4 ≤ Nat.card A) (hpts : PointsDetermined Δ) {n₀ : G}
    (hn₀ : n₀ ∈ corrN A E t) (hA : conjSub A n₀ ≠ A) (hB : conjSub A n₀ ≠ B) :
    A ⊔ B ⊔ conjSub A n₀ = corrL A E t := by
  obtain ⟨h, hX, hhA, -, hF, hcases⟩ := S.exists_torus htY hq
  obtain ⟨e₀, he₀, he₀1⟩ := S.cls.root.exists_ne_one S.tri.memE
  have hsN : partnerElt A E B e₀ ∈ corrN A E t :=
    corrM_le_corrN (S.partnerElt_mem_corrM he₀ he₀1)
  have hsB : conjSub A (partnerElt A E B e₀) = B := S.conjSub_partnerElt he₀ he₀1
  have hBh : conjSub B h = conjSub A (h * partnerElt A E B e₀ * h⁻¹) :=
    (conjSub_conj_eq hhA hsB).symm
  have hsN' : h * partnerElt A E B e₀ * h⁻¹ ∈ corrN A E t := conj_mem_corrN hX hsN
  have hconjF : ∀ f ∈ graph A t, h * f * h⁻¹ ∈ conjSub (graph A t) h := fun f hf =>
    conj_mem_conjSub h hf
  have hWh : conjSub (A ⊔ graph A t ⊔ conjSub (graph A t) h) h ≤
      A ⊔ graph A t ⊔ conjSub (graph A t) h := by
    rw [conjSub, Subgroup.map_sup, Subgroup.map_sup]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [show (A.map (MulAut.conj h).toMonoidHom) = conjSub A h from rfl, hhA]
      exact le_sup_left.trans le_sup_left
    · exact le_sup_right
    · rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      obtain ⟨f', hf', hc⟩ := hF f hf
      show h * (h * f * h⁻¹) * h⁻¹ ∈ _
      have heq : h * (h * f * h⁻¹) * h⁻¹ =
          (h * f' * h⁻¹) * f'⁻¹ * (h * f * h⁻¹) := by
        have hc' : h * (f'⁻¹ * (h * f * h⁻¹)) * h⁻¹ = f'⁻¹ * (h * f * h⁻¹) := by
          rw [hc.symm.eq, mul_inv_cancel_right]
        calc h * (h * f * h⁻¹) * h⁻¹ = h * f' * (f'⁻¹ * (h * f * h⁻¹)) * h⁻¹ := by group
          _ = (h * f' * h⁻¹) * (h * (f'⁻¹ * (h * f * h⁻¹)) * h⁻¹) := by group
          _ = (h * f' * h⁻¹) * f'⁻¹ * (h * f * h⁻¹) := by rw [hc']; group
      rw [heq]
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right (hconjF f' hf'))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.inv_mem _ hf'))))
        (Subgroup.mem_sup_right (hconjF f hf))
  have hWpow : ∀ j : ℕ, conjSub (A ⊔ graph A t ⊔ conjSub (graph A t) h) (h ^ j) ≤
      A ⊔ graph A t ⊔ conjSub (graph A t) h := by
    intro j
    induction j with
    | zero => rw [pow_zero, conjSub_one]
    | succ j ih =>
      rw [pow_succ', conjSub_mul]
      exact (Subgroup.map_mono ih).trans hWh
  have hBW : B ≤ A ⊔ graph A t := by
    intro b hb
    have ha : t⁻¹ * b * t ∈ A := by
      rw [← S.conjA] at hb
      obtain ⟨a, ha, rfl⟩ := mem_conjSub_iff.1 hb
      rwa [show t⁻¹ * (t * a * t⁻¹) * t = a by group]
    have hf : t⁻¹ * b * t * (t * (t⁻¹ * b * t) * t⁻¹) ∈ graph A t :=
      (mem_graph_iff S.commuting_conjSub).2 ⟨_, ha, rfl⟩
    have hb' : b = (t⁻¹ * b * t)⁻¹ * (t⁻¹ * b * t * (t * (t⁻¹ * b * t) * t⁻¹)) := by group
    rw [hb']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (A.inv_mem ha)) (Subgroup.mem_sup_right hf)
  have hFAB : graph A t ≤ A ⊔ B := by
    intro f hf
    obtain ⟨a, ha, rfl⟩ := (mem_graph_iff S.commuting_conjSub).1 hf
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
      (Subgroup.mem_sup_right (S.conjA ▸ conj_mem_conjSub t ha))
  have hWT : A ⊔ graph A t ⊔ conjSub (graph A t) h ≤ A ⊔ B ⊔ conjSub B h := by
    refine sup_le (sup_le (le_sup_left.trans le_sup_left) (hFAB.trans le_sup_left)) ?_
    have : conjSub (graph A t) h ≤ conjSub (A ⊔ B) h := Subgroup.map_mono hFAB
    refine this.trans ?_
    rw [conjSub, Subgroup.map_sup,
      show (A.map (MulAut.conj h).toMonoidHom) = conjSub A h from rfl, hhA]
    exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hLT : corrL A E t ≤ A ⊔ B ⊔ conjSub B h := by
    rw [S.corrL_eq_iSup htY hq]
    refine iSup₂_le fun n hn => ?_
    rcases hcases n hn with hn' | ⟨j, hj⟩
    · rw [hn']
      exact le_sup_left.trans le_sup_left
    · rw [hj]
      refine (Subgroup.map_mono (hBW.trans ?_)).trans ((hWpow j).trans hWT)
      exact le_sup_left
  have hmem : ∀ {n}, n ∈ corrN A E t → conjSub A n ∈ Δ := fun _ =>
    S.cls.root.conjSub_mem S.tri.memA _
  have hL : ∀ {C : Subgroup G}, C ≤ corrL A E t → ∀ {D : Subgroup G}, D ≤ corrL A E t →
      Commuting C D := fun hC _ hD => S.commuting_of_le_corrL htY hq hC hD
  have hAL := (le_corrL : A ≤ corrL A E t)
  have hBL : B ≤ corrL A E t := S.le_corrL_right
  have hBhL : conjSub B h ≤ corrL A E t := hBh ▸ S.conjSub_le_corrL htY hq hsN'
  have hn₀L := S.conjSub_le_corrL htY hq hn₀
  have hcardT := card_sup_sup_le S.cls S.tri.memA S.tri.memB (S.cls.root.conjSub_mem
    S.tri.memB h) (hL hAL hBL) (hL hAL hBhL) (hL hBL hBhL)
  have hcard₀ := card_sup_sup_of_ne S.cls S.iso hpts S.tri.memA S.tri.memB (hmem hn₀) S.tri.ne
    (Ne.symm hA) (Ne.symm hB) (hL hAL hBL) (hL hAL hn₀L) (hL hBL hn₀L)
  refine Subgroup.eq_of_le_of_card_ge (sup_le (sup_le hAL hBL) hn₀L) ?_
  calc Nat.card ↥(corrL A E t) ≤ Nat.card ↥(A ⊔ B ⊔ conjSub B h) :=
        Subgroup.card_le_of_le hLT
    _ ≤ Nat.card A ^ 3 := hcardT
    _ = Nat.card ↥(A ⊔ B ⊔ conjSub A n₀) := hcard₀.symm

theorem exists_conjSub_ne [Finite G] (hq : 4 ≤ Nat.card A) :
    ∃ n₀ ∈ corrN A E t, conjSub A n₀ ≠ A ∧ conjSub A n₀ ≠ B := by
  obtain ⟨h, hX, hhA, hhB, -, -⟩ := S.exists_torus htY hq
  obtain ⟨e₀, he₀, he₀1⟩ := S.cls.root.exists_ne_one S.tri.memE
  have hsN : partnerElt A E B e₀ ∈ corrN A E t :=
    corrM_le_corrN (S.partnerElt_mem_corrM he₀ he₀1)
  have hsB : conjSub A (partnerElt A E B e₀) = B := S.conjSub_partnerElt he₀ he₀1
  refine ⟨h * partnerElt A E B e₀ * h⁻¹, conj_mem_corrN hX hsN, ?_, ?_⟩ <;>
    rw [conjSub_conj_eq hhA hsB]
  · intro hBA
    have : B = A := by rw [← Aux.conjSub_conjSub_inv B h, hBA, conjSub_inv_eq hhA]
    exact S.tri.ne this.symm
  · exact hhB

theorem card_corrL [Finite G] (hq : 4 ≤ Nat.card A) (hpts : PointsDetermined Δ) :
    Nat.card ↥(corrL A E t) = Nat.card A ^ 3 := by
  obtain ⟨n₀, hn₀, hA, hB⟩ := S.exists_conjSub_ne htY hq
  have hn₀L := S.conjSub_le_corrL htY hq hn₀
  rw [← S.sup_conjSub_eq htY hq hpts hn₀ hA hB]
  exact card_sup_sup_of_ne S.cls S.iso hpts S.tri.memA S.tri.memB
    (S.cls.root.conjSub_mem S.tri.memA n₀) S.tri.ne (Ne.symm hA) (Ne.symm hB) S.tri.comm
    (S.commuting_of_le_corrL htY hq le_corrL hn₀L)
    (S.commuting_of_le_corrL htY hq S.le_corrL_right hn₀L)

theorem sup_sup_eq_corrL [Finite G] (hq : 4 ≤ Nat.card A) (hpts : PointsDetermined Δ)
    {C₁ C₂ C₃ : Subgroup G} (h₁ : C₁ ∈ Δ) (h₂ : C₂ ∈ Δ) (h₃ : C₃ ∈ Δ) (le₁ : C₁ ≤ corrL A E t)
    (le₂ : C₂ ≤ corrL A E t) (le₃ : C₃ ≤ corrL A E t) (h12 : C₁ ≠ C₂) (h13 : C₁ ≠ C₃)
    (h23 : C₂ ≠ C₃) : C₁ ⊔ C₂ ⊔ C₃ = corrL A E t := by
  refine Subgroup.eq_of_le_of_card_ge (sup_le (sup_le le₁ le₂) le₃) ?_
  rw [S.card_corrL htY hq hpts, card_sup_sup_of_ne S.cls S.iso hpts h₁ h₂ h₃ h12 h13 h23
    (S.commuting_of_le_corrL htY hq le₁ le₂) (S.commuting_of_le_corrL htY hq le₁ le₃)
    (S.commuting_of_le_corrL htY hq le₂ le₃), S.cls.root.card_eq h₁ S.tri.memA]

theorem mul_self_of_mem_corrN [Finite G] (hq : 4 ≤ Nat.card A) {n : G}
    (hn : n ∈ corrN A E t) : n * n = 1 := by
  induction hn using Subgroup.closure_induction with
  | mem n hn =>
    obtain ⟨x, -, f, hf, rfl⟩ := hn
    calc x * f * x⁻¹ * (x * f * x⁻¹) = x * (f * f) * x⁻¹ := by group
      _ = 1 := by rw [S.graph_mul_self hf, mul_one, mul_inv_cancel]
  | one => rw [mul_one]
  | mul n n' hn hn' ih ih' =>
    calc n * n' * (n * n') = n * (n' * n) * n' := by group
      _ = n * (n * n') * n' := by rw [← (S.commute_of_mem_corrN' htY hq hn hn').eq]
      _ = n * n * (n' * n') := by group
      _ = 1 := by rw [ih, ih', one_mul]
  | inv n _ ih => rw [← mul_inv_rev, ih, inv_one]

end TriangleSetting

end CFSG.Timmesfeld.Transvection
