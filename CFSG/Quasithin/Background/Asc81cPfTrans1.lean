module

public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.Quasithin.Background.Asc81cPfTen8
public import CFSG.Quasithin.Background.Asc81cPfTen6

public section

namespace CFSG.Quasithin

namespace Asc81c

namespace Pf

variable {W : Type*} [CommGroup W]

section Defs

@[expose] def Commutes (X Y : Subgroup (MulAut W)) : Prop := ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a

theorem Commutes.symm {X Y : Subgroup (MulAut W)} (h : Commutes X Y) : Commutes Y X :=
  fun a ha b hb => (h b hb a ha).symm

structure TransSetting (G : Subgroup (MulAut W)) (Ω : Set (Subgroup (MulAut W))) : Prop where
  hyp : ∀ X ∈ Ω, Hyp102 G X
  inv : ∀ g ∈ G, ∀ X ∈ Ω, X.map (MulAut.conj g).toMonoidHom ∈ Ω
  trans : ∀ X ∈ Ω, ∀ Y ∈ Ω, ∃ g ∈ G, Y = X.map (MulAut.conj g).toMonoidHom
  dich : ∀ X ∈ Ω, ∀ Y ∈ Ω, Commutes X Y ∨ X ⊔ Y = G

end Defs

section General

theorem Commutes.map_conj {X Y : Subgroup (MulAut W)} (h : Commutes X Y) (g : MulAut W) :
    Commutes (X.map (MulAut.conj g).toMonoidHom) (Y.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  show g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
  have := h a ha b hb
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [this]
    _ = _ := by group

theorem Commutes.sup {Z X Y : Subgroup (MulAut W)} (hX : Commutes Z X) (hY : Commutes Z Y) :
    Commutes Z (X ⊔ Y) := by
  intro a ha b hb
  have hle : X ⊔ Y ≤ Subgroup.centralizer {a} := sup_le
    (fun x hx => Subgroup.mem_centralizer_iff.2 fun c hc => by
      rw [Set.mem_singleton_iff.1 hc]
      exact hX a ha x hx)
    (fun y hy => Subgroup.mem_centralizer_iff.2 fun c hc => by
      rw [Set.mem_singleton_iff.1 hc]
      exact hY a ha y hy)
  exact Subgroup.mem_centralizer_iff.1 (hle hb) a (Set.mem_singleton a)

theorem commutes_self_of_isCyclic {X : Subgroup (MulAut W)} (hX : IsCyclic X) : Commutes X X :=
  fun _ ha _ hb => mul_comm_of_isCyclic hX ha hb

theorem commSub_sup (X Y : Subgroup (MulAut W)) :
    commSub (⊤ : Subgroup W) (X ⊔ Y) = commSub ⊤ X ⊔ commSub ⊤ Y := by
  have h := commSub_iSup (W := W) fun b : Bool => cond b X Y
  rw [iSup_bool_eq, iSup_bool_eq] at h
  exact h

theorem fixV_sup (X Y : Subgroup (MulAut W)) : fixV (X ⊔ Y) = fixV X ⊓ fixV Y :=
  CFSG.Quasithin.FixVLat.fixV_sup_eq X Y

theorem map_conj_eq_of_commutes {X : Subgroup (MulAut W)} {g : MulAut W}
    (h : ∀ x ∈ X, g * x = x * g) : X.map (MulAut.conj g).toMonoidHom = X := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show g * x * g⁻¹ ∈ X
    rw [h x hx, mul_inv_cancel_right]
    exact hx
  · intro hy
    refine ⟨y, hy, ?_⟩
    show g * y * g⁻¹ = y
    rw [h y hy, mul_inv_cancel_right]

theorem map_conj_injective (g : MulAut W) :
    Function.Injective fun X : Subgroup (MulAut W) => X.map (MulAut.conj g).toMonoidHom :=
  Subgroup.map_injective (MulAut.conj g).injective

variable [Finite W]

theorem card_sup_le (A B : Subgroup W) : Nat.card ↥(A ⊔ B) ≤ Nat.card A * Nat.card B := by
  have h := card_sup_mul_card_inf A B
  have hpos : 0 < Nat.card ↥(A ⊓ B) := Nat.card_pos
  rw [← h]
  exact Nat.le_mul_of_pos_right _ hpos

omit [Finite W] in
theorem card_sup_of_inf_eq_bot {A B : Subgroup W} (h : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have h1 := card_sup_mul_card_inf A B
  rw [h, Subgroup.card_bot, mul_one] at h1
  exact h1

theorem finite_subgroups : Finite (Subgroup (MulAut W)) := by
  have := finite_mulAut (W := W)
  exact Finite.of_injective (SetLike.coe : Subgroup (MulAut W) → Set (MulAut W))
    SetLike.coe_injective

end General

section Trans

variable [Finite W] {G : Subgroup (MulAut W)} {Ω : Set (Subgroup (MulAut W))}
  {X₀ Y₀ : Subgroup (MulAut W)}

omit [Finite W] in
theorem TransSetting.card_eq (hT : TransSetting G Ω) (hX₀ : X₀ ∈ Ω) {Z : Subgroup (MulAut W)}
    (hZ : Z ∈ Ω) : Nat.card Z = Nat.card X₀ := by
  obtain ⟨g, -, rfl⟩ := hT.trans X₀ hX₀ Z hZ
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem TransSetting.card_commSub_eq (hT : TransSetting G Ω) (hX₀ : X₀ ∈ Ω)
    {Z : Subgroup (MulAut W)} (hZ : Z ∈ Ω) :
    Nat.card (commSub (⊤ : Subgroup W) Z) = Nat.card (commSub (⊤ : Subgroup W) X₀) := by
  rw [card_commSub (hT.hyp Z hZ).1, card_commSub (hT.hyp X₀ hX₀).1, hT.card_eq hX₀ hZ]

omit [Finite W] in
theorem TransSetting.exists_not_commutes (hT : TransSetting G Ω) (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω)
    (hnc : ¬ Commutes X₀ Y₀) {Z : Subgroup (MulAut W)} (hZ : Z ∈ Ω) :
    ∃ Z' ∈ Ω, ¬ Commutes Z Z' := by
  by_contra hall
  push Not at hall
  have hG : X₀ ⊔ Y₀ = G := (hT.dich X₀ hX₀ Y₀ hY₀).resolve_left hnc
  have hZG : Commutes Z G := hG ▸ (hall X₀ hX₀).sup (hall Y₀ hY₀)
  have hconj : ∀ g ∈ G, Z.map (MulAut.conj g).toMonoidHom = Z := fun g hg =>
    map_conj_eq_of_commutes fun z hz => (hZG z hz g hg).symm
  obtain ⟨g₁, hg₁, hX⟩ := hT.trans Z hZ X₀ hX₀
  obtain ⟨g₂, hg₂, hY⟩ := hT.trans Z hZ Y₀ hY₀
  rw [hconj g₁ hg₁] at hX
  rw [hconj g₂ hg₂] at hY
  apply hnc
  rw [hX, hY]
  exact commutes_self_of_isCyclic (hT.hyp Z hZ).1.2.2.1

omit [Finite W] in
theorem TransSetting.commSub_eq_sup (hT : TransSetting G Ω) {Z Z' : Subgroup (MulAut W)}
    (hZ : Z ∈ Ω) (hZ' : Z' ∈ Ω) (hnc : ¬ Commutes Z Z') :
    commSub (⊤ : Subgroup W) G = commSub ⊤ Z ⊔ commSub ⊤ Z' := by
  rw [← (hT.dich Z hZ Z' hZ').resolve_left hnc, commSub_sup]

theorem TransSetting.not_commutes (hW : ∀ w : W, w ^ 2 = 1) (hT : TransSetting G Ω)
    (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω) (hnc : ¬ Commutes X₀ Y₀) :
    ∀ Z ∈ Ω, ∀ Z' ∈ Ω, Z ≠ Z' → ¬ Commutes Z Z' := by
  classical
  intro Z hZ Z' hZ' hne hc
  have hfin := finite_subgroups (W := W)
  have hh : ∀ J ∈ Ω, Hyp101 G J := fun J hJ => (hT.hyp J hJ).1
  set q := Nat.card (commSub (⊤ : Subgroup W) X₀) with hqdef
  have hq : ∀ J ∈ Ω, Nat.card (commSub (⊤ : Subgroup W) J) = q := fun J hJ =>
    hT.card_commSub_eq hX₀ hJ
  have hq4 : 4 ≤ q := by
    have h1 := card_commSub (hh X₀ hX₀)
    have h2 : Nat.card X₀ ≠ 1 := fun h0 => (hh X₀ hX₀).2.1 (Subgroup.eq_bot_of_card_eq X₀ h0)
    obtain ⟨m, hm⟩ := (hh X₀ hX₀).2.2.2.1
    omega
  have hGle : Nat.card (commSub (⊤ : Subgroup W) G) ≤ q * q := by
    rw [hT.commSub_eq_sup hX₀ hY₀ hnc]
    exact (card_sup_le _ _).trans (by rw [hq X₀ hX₀, hq Y₀ hY₀])
  have hZZ' : commSub (⊤ : Subgroup W) Z ⊓ commSub ⊤ Z' = ⊥ :=
    commSub_inf_commSub_eq_bot hW (hh Z hZ) (hh Z' hZ') hne hc
  have hGeq : commSub (⊤ : Subgroup W) G = commSub ⊤ Z ⊔ commSub ⊤ Z' := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (sup_le (commSub_mono le_rfl (hh Z hZ).1)
      (commSub_mono le_rfl (hh Z' hZ').1)) ?_
    rw [card_sup_of_inf_eq_bot hZZ', hq Z hZ, hq Z' hZ']
    exact hGle
  have hGq : Nat.card (commSub (⊤ : Subgroup W) G) = q * q := by
    rw [hGeq, card_sup_of_inf_eq_bot hZZ', hq Z hZ, hq Z' hZ']
  have huniq : ∀ J ∈ Ω, ∀ J₁ ∈ Ω, ∀ J₂ ∈ Ω, J₁ ≠ J → J₂ ≠ J → Commutes J J₁ → Commutes J J₂ →
      J₁ = J₂ := by
    intro J hJ J₁ hJ₁ J₂ hJ₂ h1 h2 hc1 hc2
    by_contra h12
    by_cases hc12 : Commutes J₁ J₂
    ·
      have hA : commSub (⊤ : Subgroup W) J ⊓ commSub ⊤ J₁ = ⊥ :=
        commSub_inf_commSub_eq_bot hW (hh J hJ) (hh J₁ hJ₁) (Ne.symm h1) hc1
      have hB : (commSub (⊤ : Subgroup W) J ⊔ commSub ⊤ J₁) ⊓ commSub ⊤ J₂ = ⊥ := by
        rw [eq_bot_iff]
        rintro w ⟨hw1, hw2⟩
        have hfix : commSub (⊤ : Subgroup W) J ⊔ commSub ⊤ J₁ ≤ fixV J₂ := sup_le
          (commSub_le_fixV_of_commute hW (hh J hJ) (hh J₂ hJ₂) (Ne.symm h2) hc2)
          (commSub_le_fixV_of_commute hW (hh J₁ hJ₁) (hh J₂ hJ₂) h12 hc12)
        have h3 : w ∈ fixV J₂ ⊓ commSub ⊤ J₂ := ⟨hfix hw1, hw2⟩
        rwa [fixV_inf_commSub_eq_bot' hW (hh J₂ hJ₂).2.2.2.1] at h3
      have hle : (commSub (⊤ : Subgroup W) J ⊔ commSub ⊤ J₁) ⊔ commSub ⊤ J₂ ≤
          commSub (⊤ : Subgroup W) G :=
        sup_le (sup_le (commSub_mono le_rfl (hh J hJ).1) (commSub_mono le_rfl (hh J₁ hJ₁).1))
          (commSub_mono le_rfl (hh J₂ hJ₂).1)
      have h3 := Subgroup.card_le_of_le hle
      rw [card_sup_of_inf_eq_bot hB, card_sup_of_inf_eq_bot hA, hq J hJ, hq J₁ hJ₁, hq J₂ hJ₂,
        hGq] at h3
      have h4 : q * q * 4 ≤ q * q * q := Nat.mul_le_mul_left _ hq4
      nlinarith
    ·
      have hG : J₁ ⊔ J₂ = G := (hT.dich J₁ hJ₁ J₂ hJ₂).resolve_left hc12
      obtain ⟨J', hJ', hnc'⟩ := hT.exists_not_commutes hX₀ hY₀ hnc hJ
      exact hnc' fun a ha b hb => (hG ▸ hc1.sup hc2) a ha b ((hh J' hJ').1 hb)
  have hpartner : ∀ J ∈ Ω, ∃ J' ∈ Ω, J' ≠ J ∧ Commutes J J' := by
    intro J hJ
    obtain ⟨g, hg, rfl⟩ := hT.trans Z hZ J hJ
    refine ⟨Z'.map (MulAut.conj g).toMonoidHom, hT.inv g hg Z' hZ', fun h => hne ?_,
      hc.map_conj g⟩
    exact (map_conj_injective g h).symm
  have hdisj : ∀ J ∈ Ω, ∀ J' ∈ Ω, J ≠ J' →
      commSub (⊤ : Subgroup W) J ⊓ commSub ⊤ J' = ⊥ := by
    intro J hJ J' hJ' hJJ'
    by_cases hcJ : Commutes J J'
    · exact commSub_inf_commSub_eq_bot hW (hh J hJ) (hh J' hJ') hJJ' hcJ
    · have h1 := hT.commSub_eq_sup hJ hJ' hcJ
      have h2 := card_sup_mul_card_inf (commSub (⊤ : Subgroup W) J) (commSub ⊤ J')
      rw [← h1, hGq, hq J hJ, hq J' hJ'] at h2
      have hpos : 0 < q * q := by positivity
      have h3 : Nat.card ↥(commSub (⊤ : Subgroup W) J ⊓ commSub ⊤ J') = 1 := by
        have := Nat.eq_of_mul_eq_mul_left hpos (h2.trans (mul_one (q * q)).symm)
        exact this
      exact Subgroup.eq_bot_of_card_eq _ h3
  have hsemi : ∀ J ∈ Ω, J ≠ Z → J ≠ Z' → ∀ x ∈ Z,
      J.map (MulAut.conj x).toMonoidHom = J → x = 1 := by
    intro J hJ hJZ hJZ' x hx hxJ
    by_contra hx1
    obtain ⟨w, hw, hw1⟩ := exists_ne_one (hh J hJ)
    have hwG : w ∈ commSub (⊤ : Subgroup W) Z ⊔ commSub ⊤ Z' := by
      rw [← hGeq]
      exact commSub_mono le_rfl (hh J hJ).1 hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hwG
    have hxb : x b = b :=
      commSub_le_fixV_of_commute hW (hh Z' hZ') (hh Z hZ) (Ne.symm hne) hc.symm hb x hx
    have hxw : x (a * b) ∈ commSub (⊤ : Subgroup W) J := by
      have h1 := mem_commSub_map_conj J x hw
      rwa [hxJ] at h1
    have h2 : x a * a⁻¹ ∈ commSub (⊤ : Subgroup W) J ⊓ commSub ⊤ Z := by
      refine ⟨?_, (commSub ⊤ Z).mul_mem (commSub_stable' hx ha) ((commSub ⊤ Z).inv_mem ha)⟩
      have h3 := (commSub ⊤ J).mul_mem hxw ((commSub ⊤ J).inv_mem hw)
      have h4 : x (a * b) * (a * b)⁻¹ = x a * a⁻¹ := by
        rw [map_mul, hxb, mul_inv_rev, mul_comm b⁻¹, mul_assoc, ← mul_assoc b, mul_comm b a⁻¹,
          mul_assoc, mul_inv_cancel, mul_one]
      rwa [h4] at h3
    rw [hdisj J hJ Z hZ hJZ] at h2
    have hxa : x a = a := mul_inv_eq_one.1 h2
    have ha1 : a = 1 := by
      by_contra ha1
      exact hx1 (eq_one_of_apply_eq (hh Z hZ) hx ha ha1 hxa)
    rw [ha1, one_mul] at hw hw1
    have h3 : b ∈ commSub (⊤ : Subgroup W) J ⊓ commSub ⊤ Z' := ⟨hw, hb⟩
    rw [hdisj J hJ Z' hZ' hJZ'] at h3
    exact hw1 h3
  have hΩfin : Ω.Finite := Set.toFinite Ω
  have hcount : Ω.ncard * (q - 1) ≤ q * q - 1 := by
    have : Fintype W := Fintype.ofFinite W
    let S : Subgroup (MulAut W) → Finset W := fun J =>
      ((commSub (⊤ : Subgroup W) J : Set W) \ {1}).toFinset
    have hSd : (hΩfin.toFinset : Set (Subgroup (MulAut W))).PairwiseDisjoint S := by
      intro J hJ J' hJ' hJJ'
      rw [Function.onFun, Finset.disjoint_left]
      intro w hw hw'
      simp only [S, Set.mem_toFinset, Set.mem_sdiff, SetLike.mem_coe,
        Set.mem_singleton_iff] at hw hw'
      have h1 : w ∈ commSub (⊤ : Subgroup W) J ⊓ commSub ⊤ J' := ⟨hw.1, hw'.1⟩
      rw [hdisj J (hΩfin.mem_toFinset.1 hJ) J' (hΩfin.mem_toFinset.1 hJ') hJJ'] at h1
      exact hw.2 h1
    have hsub : hΩfin.toFinset.biUnion S ⊆
        ((commSub (⊤ : Subgroup W) G : Set W) \ {1}).toFinset := by
      intro w hw
      simp only [Finset.mem_biUnion, S, Set.mem_toFinset, Set.mem_sdiff, SetLike.mem_coe,
        Set.mem_singleton_iff] at hw ⊢
      obtain ⟨J, hJ, hw1, hw2⟩ := hw
      exact ⟨commSub_mono le_rfl (hh J (hΩfin.mem_toFinset.1 hJ)).1 hw1, hw2⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_biUnion hSd] at h1
    have hS : ∀ J ∈ hΩfin.toFinset, (S J).card = q - 1 := by
      intro J hJ
      simp only [S]
      rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, card_diff_one,
        hq J (hΩfin.mem_toFinset.1 hJ)]
    rw [Finset.sum_congr rfl hS, Finset.sum_const, smul_eq_mul, Set.toFinset_card,
      ← Nat.card_eq_fintype_card, card_diff_one, hGq] at h1
    rwa [← Set.ncard_eq_toFinset_card Ω hΩfin] at h1
  have hcardZ : Nat.card Z = q - 1 := by
    have := card_commSub (hh Z hZ)
    rw [hq Z hZ] at this
    omega
  have hΩle : Ω.ncard ≤ q + 1 := by
    obtain ⟨a, ha⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
    rw [ha] at hcount ⊢
    have h1 : (a + 1) * (a + 1) - 1 = a * (a + 2) := by
      rw [show (a + 1) * (a + 1) = a * (a + 2) + 1 by ring, Nat.add_sub_cancel]
    rw [h1, Nat.add_sub_cancel, mul_comm] at hcount
    have h2 : 0 < a := by omega
    have h3 := Nat.le_of_mul_le_mul_left hcount h2
    omega
  obtain ⟨J₀, hJ₀, hJ₀nc⟩ := hT.exists_not_commutes hX₀ hY₀ hnc hZ
  have hJ₀Z : J₀ ≠ Z := by
    rintro rfl
    exact hJ₀nc (commutes_self_of_isCyclic (hh J₀ hJ₀).2.2.1)
  have hJ₀Z' : J₀ ≠ Z' := by
    rintro rfl
    exact hJ₀nc hc
  let T : Set (Subgroup (MulAut W)) := Ω \ {Z, Z'}
  have hmemT : ∀ J, J ∈ T ↔ J ∈ Ω ∧ J ≠ Z ∧ J ≠ Z' := by
    intro J
    simp only [T, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  have hconjT : ∀ x ∈ Z, J₀.map (MulAut.conj x).toMonoidHom ∈ T := by
    intro x hx
    refine (hmemT _).2 ⟨hT.inv x ((hh Z hZ).1 hx) J₀ hJ₀, fun h => hJ₀Z ?_, fun h => hJ₀Z' ?_⟩
    · have h1 : Z.map (MulAut.conj x).toMonoidHom = Z :=
        map_conj_eq_of_commutes fun z hz => mul_comm_of_isCyclic (hh Z hZ).2.2.1 hx hz
      rw [← h1] at h
      exact map_conj_injective x h
    · have h1 : Z'.map (MulAut.conj x).toMonoidHom = Z' :=
        map_conj_eq_of_commutes fun z hz => hc x hx z hz
      rw [← h1] at h
      exact map_conj_injective x h
  let f : Z → T := fun x => ⟨_, hconjT x x.2⟩
  have hf : Function.Injective f := by
    intro x x' hxx
    have h1 : J₀.map (MulAut.conj (x : MulAut W)).toMonoidHom =
        J₀.map (MulAut.conj (x' : MulAut W)).toMonoidHom := congrArg Subtype.val hxx
    have h2 : J₀.map (MulAut.conj ((x' : MulAut W)⁻¹ * x)).toMonoidHom = J₀ := by
      rw [← map_conj_map_conj, h1, map_conj_map_conj, inv_mul_cancel, map_conj_one]
    have h3 := hsemi J₀ hJ₀ hJ₀Z hJ₀Z' _ (Z.mul_mem (Z.inv_mem x'.2) x.2) h2
    apply Subtype.ext
    rw [inv_mul_eq_one] at h3
    exact h3.symm
  have hTcard : Nat.card T = Ω.ncard - 2 := by
    rw [Nat.card_coe_set_eq]
    have hsub : ({Z, Z'} : Set (Subgroup (MulAut W))) ⊆ Ω := by
      intro J hJ
      rcases hJ with rfl | rfl
      · exact hZ
      · exact hZ'
    rw [Set.ncard_sdiff hsub, Set.ncard_pair hne]
  have hbij : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by rw [hTcard, hcardZ]; omega)
  obtain ⟨J₁, hJ₁, hJ₁J₀, hcJ₁⟩ := hpartner J₀ hJ₀
  have hJ₁T : J₁ ∈ T := by
    refine (hmemT J₁).2 ⟨hJ₁, fun h => hJ₀nc ?_, fun h => hJ₀Z ?_⟩
    · rw [h] at hcJ₁
      exact hcJ₁.symm
    · rw [h] at hcJ₁ hJ₁J₀
      exact huniq Z' hZ' J₀ hJ₀ Z hZ hJ₀Z' hne hcJ₁.symm hc.symm
  obtain ⟨⟨x₀, hx₀⟩, hx₀J⟩ := hbij.2 ⟨J₁, hJ₁T⟩
  have hx₀J' : J₀.map (MulAut.conj x₀).toMonoidHom = J₁ := congrArg Subtype.val hx₀J
  have hc2 : Commutes J₁ (J₁.map (MulAut.conj x₀).toMonoidHom) := by
    have := hcJ₁.map_conj x₀
    rwa [hx₀J'] at this
  have hne2 : J₁.map (MulAut.conj x₀).toMonoidHom ≠ J₁ := fun h =>
    hJ₁J₀ (map_conj_injective x₀ (h.trans hx₀J'.symm))
  have hmem2 : J₁.map (MulAut.conj x₀).toMonoidHom ∈ Ω := hT.inv x₀ ((hh Z hZ).1 hx₀) J₁ hJ₁
  have h3 := huniq J₁ hJ₁ _ hmem2 J₀ hJ₀ hne2 (Ne.symm hJ₁J₀) hc2 hcJ₁.symm
  have h4 : J₀.map (MulAut.conj (x₀ * x₀)).toMonoidHom = J₀ := by
    rw [← map_conj_map_conj, hx₀J', h3]
  have h5 := hsemi J₀ hJ₀ hJ₀Z hJ₀Z' _ (Z.mul_mem hx₀ hx₀) h4
  have hodd := odd_orderOf_of_mem (hh Z hZ).2.2.2.1 hx₀
  have h6 : orderOf x₀ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h5)
  have h7 : orderOf x₀ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h6 with h8 | h8
    · exact h8
    · rw [h8] at hodd
      exact absurd hodd (by decide)
  rw [orderOf_eq_one_iff.1 h7, map_conj_one] at hx₀J'
  exact hJ₁J₀ hx₀J'.symm

theorem TransSetting.fixV_inf_eq (hW : ∀ w : W, w ^ 2 = 1) (hT : TransSetting G Ω)
    (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω) (hnc : ¬ Commutes X₀ Y₀) {Z Z' : Subgroup (MulAut W)}
    (hZ : Z ∈ Ω) (hZ' : Z' ∈ Ω) (hne : Z ≠ Z') : fixV Z ⊓ fixV Z' = fixV G := by
  rw [← fixV_sup, (hT.dich Z hZ Z' hZ').resolve_left
    (hT.not_commutes hW hX₀ hY₀ hnc Z hZ Z' hZ' hne)]

theorem TransSetting.exists_third (hW : ∀ w : W, w ^ 2 = 1) (hT : TransSetting G Ω)
    (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω) (hnc : ¬ Commutes X₀ Y₀) : ∃ K ∈ Ω, K ≠ X₀ ∧ K ≠ Y₀ := by
  by_contra hall
  push Not at hall
  have hcyc := (hT.hyp Y₀ hY₀).1.2.2.1
  have hXY : X₀ ≠ Y₀ := by
    rintro rfl
    exact hnc (commutes_self_of_isCyclic hcyc)
  have hYN : Y₀ ≤ Subgroup.normalizer (X₀ : Set (MulAut W)) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    by_contra h2
    have h3 := hall _ (hT.inv y ((hT.hyp Y₀ hY₀).1.1 hy) X₀ hX₀) h2
    have h4 : Y₀.map (MulAut.conj y⁻¹).toMonoidHom = Y₀ :=
      map_conj_eq_of_commutes fun z hz => mul_comm_of_isCyclic hcyc (Y₀.inv_mem hy) hz
    apply hXY
    have h5 := congrArg (fun X : Subgroup (MulAut W) => X.map (MulAut.conj y⁻¹).toMonoidHom) h3
    simp only [map_conj_map_conj, inv_mul_cancel, map_conj_one, h4] at h5
    exact h5
  have hnc' : ∃ x ∈ X₀, ∃ y ∈ Y₀, x * y ≠ y * x := by
    by_contra h0
    push Not at h0
    exact hnc h0
  obtain ⟨h7, h3⟩ := ten_six hW (hT.hyp X₀ hX₀).1 (hT.hyp Y₀ hY₀).1 hYN hnc'
  have h8 := hT.card_eq hX₀ hY₀
  omega

end Trans

end Pf

end Asc81c

end CFSG.Quasithin
