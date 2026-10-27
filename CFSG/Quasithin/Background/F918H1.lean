module

public import CFSG.Quasithin.Background.F918H0
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122ASimple
public import CFSG.Quasithin.Background.F918P2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Matrix commutatorElement

section Elementary

variable {W : Type} [CommGroup W]

private theorem conjAutSub_mul_d36 (a b : MulAut W) (L : Subgroup (MulAut W)) :
    conjAutSub (a * b) L = conjAutSub a (conjAutSub b L) := by
  ext x
  simp only [mem_conjAutSub_iff]
  have : (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
  rw [this]

private theorem mem_normalizer_of_conjAutSub_eq_d36 {L : Subgroup (MulAut W)} {s : MulAut W}
    (h : conjAutSub s L = L) : s ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

private def commHomD36 (g : MulAut W) : W →* W where
  toFun w := g w * w⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv_rev]
    ac_rfl

private theorem commSub_eq_commOf_d36 (X : Subgroup (MulAut W)) (U : Subgroup W) :
    commSub U X = XMod.commOf ↥X U := by
  unfold commSub XMod.commOf
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, w, hw, rfl⟩
    exact ⟨⟨x, hx⟩, w, hw, rfl⟩
  · rintro ⟨⟨x, hx⟩, w, hw, rfl⟩
    exact ⟨x, hx, w, hw, rfl⟩

private theorem mem_commSub_map_d36 {X : Subgroup (MulAut W)} {U : Subgroup W} {s : MulAut W}
    (hs : s ∈ Subgroup.normalizer (X : Set (MulAut W))) (hU : ∀ w ∈ U, s w ∈ U) :
    ∀ u ∈ commSub U X, s u ∈ commSub U X := by
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, w, hw, rfl⟩ := hc
    have hx' : s * x * s⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hs x).mp hx
    refine Subgroup.subset_closure ⟨s * x * s⁻¹, hx', s w, hU w hw, ?_⟩
    simp [MulAut.mul_apply]
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

end Elementary

section Norm

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

private theorem d36_clause (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    A38Types ↥L ∧ ⁅L, conjAutSub t L⁆ = ⊥ ∧ L ⊓ conjAutSub t L = ⊥ ∧
      ∀ s ∈ T, conjAutSub s L = L ∨ conjAutSub s L = conjAutSub t L :=
  hL38 W M Mp T L V n.std t n.tT n.tn n.Mp_eq

private theorem conjAutSub_eq_of_not_mem_d36 (hL38 : D3L38) (n : D36Norm M Mp T L V t)
    {s : MulAut W} (hs : s ∈ T) (hsn : s ∉ Subgroup.normalizer (L : Set (MulAut W))) :
    conjAutSub s L = conjAutSub t L := by
  rcases (d36_clause hL38 n).2.2.2 s hs with h | h
  · exact absurd (mem_normalizer_of_conjAutSub_eq_d36 h) hsn
  · exact h

private theorem d36_inv_V (n : D36Norm M Mp T L V t) {g : MulAut W} (hg : g ∈ Mp) {v : W}
    (hv : v ∈ V) : g v ∈ V :=
  n.std.hyp.irr.2.1 ⟨g, hg⟩ v hv

private theorem d36_L_le_Mp (n : D36Norm M Mp T L V t) : L ≤ Mp := by
  rw [n.Mp_eq]
  exact le_sup_left

private theorem d36_Lt_le_Mp (n : D36Norm M Mp T L V t) : conjAutSub t L ≤ Mp := by
  rw [n.Mp_eq]
  exact le_sup_right

theorem d36_split (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    ∀ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) ∨
      t⁻¹ * s ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
  intro s hs
  by_cases hsn : s ∈ Subgroup.normalizer (L : Set (MulAut W))
  · exact Or.inl hsn
  · right
    have h := conjAutSub_eq_of_not_mem_d36 hL38 n hs hsn
    apply mem_normalizer_of_conjAutSub_eq_d36
    rw [conjAutSub_mul_d36, h, conjAutSub_inv_conjAutSub]

private theorem commSub_Mp_le_d36 (n : D36Norm M Mp T L V t) : commSub V Mp ≤ commSub V L := by
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨g, hg, v, hv, rfl⟩
  have hg' : g ∈ Subgroup.closure ((L : Set (MulAut W)) ∪ (conjAutSub t L : Set (MulAut W))) := by
    rw [← Subgroup.sup_eq_closure, ← n.Mp_eq]
    exact hg
  have key : ∀ g (_ : g ∈ Subgroup.closure
      ((L : Set (MulAut W)) ∪ (conjAutSub t L : Set (MulAut W)))),
      g ∈ Mp ∧ ∀ v ∈ V, g v * v⁻¹ ∈ commSub V L := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with hg | hg
      · exact ⟨d36_L_le_Mp n hg, fun v hv => Subgroup.subset_closure ⟨g, hg, v, hv, rfl⟩⟩
      · refine ⟨d36_Lt_le_Mp n hg, fun v hv => ?_⟩
        rw [n.triv v hv g hg, mul_inv_cancel]
        exact one_mem _
    | one => exact ⟨one_mem _, fun v hv => by simp⟩
    | mul a b _ _ ha hb =>
      refine ⟨mul_mem ha.1 hb.1, fun v hv => ?_⟩
      have hbv : b v ∈ V := d36_inv_V n hb.1 hv
      have : (a * b) v * v⁻¹ = (a (b v) * (b v)⁻¹) * (b v * v⁻¹) := by
        simp only [MulAut.mul_apply]
        group
      rw [this]
      exact mul_mem (ha.2 _ hbv) (hb.2 v hv)
    | inv a _ ha =>
      refine ⟨inv_mem ha.1, fun v hv => ?_⟩
      have hav : a⁻¹ v ∈ V := d36_inv_V n (inv_mem ha.1) hv
      have h2 := ha.2 _ hav
      have : a⁻¹ v * v⁻¹ = (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ := by
        simp
      rw [this]
      exact inv_mem h2
  exact (key g hg').2 v hv

theorem d36_V_le_U (_hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    V ≤ commSub (orbSup T V) L := by
  have h1 : commSub V Mp = V := by
    rw [commSub_eq_commOf_d36]
    exact n.std.hyp.irr.2.2.1
  calc V = commSub V Mp := h1.symm
    _ ≤ commSub V L := commSub_Mp_le_d36 n
    _ ≤ commSub (orbSup T V) L := commSub_mono (le_orbSup T V) le_rfl

private theorem d36_triv_smul (hL38 : D3L38) (n : D36Norm M Mp T L V t) {x : MulAut W}
    (hx : x ∈ T) (hxn : x ∉ Subgroup.normalizer (L : Set (MulAut W))) {g : MulAut W}
    (hg : g ∈ L) {v : W} (hv : v ∈ V) : g (x v) = x v := by
  have hxinv : x⁻¹ ∈ T := T.inv_mem hx
  have hxinvn : x⁻¹ ∉ Subgroup.normalizer (L : Set (MulAut W)) := fun h =>
    hxn (by simpa using inv_mem h)
  have h1 := conjAutSub_eq_of_not_mem_d36 hL38 n hxinv hxinvn
  have h2 : x⁻¹ * g * x ∈ conjAutSub t L := by
    rw [← h1, mem_conjAutSub_iff]
    simpa [mul_assoc] using hg
  have h3 := n.triv v hv _ h2
  calc g (x v) = x ((x⁻¹ * g * x) v) := by simp [MulAut.mul_apply]
    _ = x v := by rw [h3]

private theorem d36_conj_conj (hL38 : D3L38) (n : D36Norm M Mp T L V t) {s : MulAut W}
    (hs : s ∈ T) (hsn : s ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    conjAutSub s (conjAutSub t L) = conjAutSub t L := by
  have hst : s * t ∈ T := T.mul_mem hs n.tT
  have hstn : s * t ∉ Subgroup.normalizer (L : Set (MulAut W)) := by
    intro h
    apply n.tn
    have := mul_mem (inv_mem hsn) h
    simpa using this
  rw [← conjAutSub_mul_d36]
  exact conjAutSub_eq_of_not_mem_d36 hL38 n hst hstn

theorem d36_U_eq (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    commSub (orbSup T V) L = orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V := by
  set S := T ⊓ Subgroup.normalizer (L : Set (MulAut W)) with hS
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨g, hg, w, hw, rfl⟩
    have hle : orbSup T V ≤ (orbSup S V).comap (commHomD36 g) := by
      refine orbSup_le fun x hx => ?_
      rintro _ ⟨v, hv, rfl⟩
      show g (x v) * (x v)⁻¹ ∈ orbSup S V
      by_cases hxn : x ∈ Subgroup.normalizer (L : Set (MulAut W))
      · have hxS : x ∈ S := ⟨hx, hxn⟩
        have h1 : x⁻¹ * g * x ∈ L := by
          have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxn) g).mp hg
          simpa using this
        have h2 : (x⁻¹ * g * x) v ∈ V := d36_inv_V n (d36_L_le_Mp n h1) hv
        have h3 : g (x v) * (x v)⁻¹ = x ((x⁻¹ * g * x) v * v⁻¹) := by
          simp [MulAut.mul_apply]
        rw [h3]
        exact map_le_orbSup hxS ⟨_, V.mul_mem h2 (V.inv_mem hv), rfl⟩
      · rw [d36_triv_smul hL38 n hx hxn hg hv, mul_inv_cancel]
        exact one_mem _
    exact hle hw
  · refine orbSup_le fun s hs => ?_
    rintro _ ⟨v, hv, rfl⟩
    exact mem_commSub_map_d36 hs.2 (fun w hw => mem_orbSup_of_mem_map hs.1 hw) v
      (d36_V_le_U hL38 n hv)

theorem d36_part1 (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    IsSumMod (orbSup T V ⊓ fixV Mp) (commSub (orbSup T V) L)
      ((commSub (orbSup T V) L).map t.toMonoidHom) (orbSup T V) ∧
    ∀ u ∈ commSub (orbSup T V) L, ∀ g ∈ conjAutSub t L, g u = u := by
  set S := T ⊓ Subgroup.normalizer (L : Set (MulAut W)) with hS
  have hU := d36_U_eq hL38 n
  have h2 : ∀ u ∈ commSub (orbSup T V) L, ∀ g ∈ conjAutSub t L, g u = u := by
    intro u hu g hg
    rw [hU] at hu
    have hle : orbSup S V ≤ fixV (conjAutSub t L) := by
      refine orbSup_le fun s hs => ?_
      rintro _ ⟨v, hv, rfl⟩ g hg
      have hg' : g ∈ conjAutSub s (conjAutSub t L) := by
        rw [d36_conj_conj hL38 n hs.1 hs.2]
        exact hg
      have h1 : s⁻¹ * g * s ∈ conjAutSub t L := mem_conjAutSub_iff.mp hg'
      calc g (s v) = s ((s⁻¹ * g * s) v) := by simp [MulAut.mul_apply]
        _ = s v := by rw [n.triv v hv _ h1]
    exact hle hu g hg
  have hUt : ∀ u ∈ commSub (orbSup T V) L, ∀ g ∈ L, g (t u) = t u := by
    intro u hu g hg
    have h1 : conjAutSub t⁻¹ L = conjAutSub t L :=
      conjAutSub_eq_of_not_mem_d36 hL38 n (T.inv_mem n.tT)
        (fun h => n.tn (by simpa using inv_mem h))
    have h3 : t⁻¹ * g * t ∈ conjAutSub t L := by
      rw [← h1, mem_conjAutSub_iff]
      simpa [mul_assoc] using hg
    calc g (t u) = t ((t⁻¹ * g * t) u) := by simp [MulAut.mul_apply]
      _ = t u := by rw [h2 u hu _ h3]
  have hUle : commSub (orbSup T V) L ≤ orbSup T V := by
    rw [hU]
    exact orbSup_le fun s hs => map_le_orbSup hs.1
  have hUtle : (commSub (orbSup T V) L).map t.toMonoidHom ≤ orbSup T V := by
    rintro _ ⟨u, hu, rfl⟩
    exact mem_orbSup_of_mem_map n.tT (hUle hu)
  refine ⟨⟨?_, ?_⟩, h2⟩
  · apply le_antisymm
    · refine orbSup_le fun x hx => ?_
      rcases d36_split hL38 n x hx with h | h
      · have h1 : V.map x.toMonoidHom ≤ orbSup S V := map_le_orbSup ⟨hx, h⟩
        rw [← hU] at h1
        exact h1.trans (le_sup_left.trans le_sup_left)
      · have hs : t⁻¹ * x ∈ S := ⟨T.mul_mem (T.inv_mem n.tT) hx, h⟩
        have h1 : V.map x.toMonoidHom ≤ (orbSup S V).map t.toMonoidHom := by
          rintro _ ⟨v, hv, rfl⟩
          refine ⟨(t⁻¹ * x) v, map_le_orbSup hs ⟨v, hv, rfl⟩, ?_⟩
          simp [MulAut.mul_apply]
        rw [← hU] at h1
        exact h1.trans (le_sup_right.trans le_sup_left)
    · exact sup_le (sup_le hUle hUtle) inf_le_left
  · intro w hw
    obtain ⟨hw1, hw2⟩ := hw
    obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.mp hw1
    obtain ⟨u', hu', c', hc', hw⟩ := Subgroup.mem_sup.mp hw2
    obtain ⟨u₀, hu₀, rfl⟩ := hu'
    have hLfix : ∀ g ∈ L, g u = u := by
      intro g hg
      have e1 : g (t.toMonoidHom u₀) = t.toMonoidHom u₀ := hUt u₀ hu₀ g hg
      have e2 : g (t.toMonoidHom u₀ * c') = t.toMonoidHom u₀ * c' := by
        rw [map_mul, e1, hc'.2 g (d36_L_le_Mp n hg)]
      rw [hw, map_mul, hc.2 g (d36_L_le_Mp n hg)] at e2
      exact mul_right_cancel e2
    have hfixu : ∀ g ∈ Mp, g u = u := by
      intro g hg
      have hMpLe : Mp ≤ MulAction.stabilizer (MulAut W) u := by
        rw [n.Mp_eq]
        exact sup_le (fun g hg => hLfix g hg) (fun g hg => h2 u hu g hg)
      exact hMpLe hg
    refine ⟨?_, ?_⟩
    · exact (orbSup T V).mul_mem (hUle hu) hc.1
    · intro g hg
      rw [map_mul, hfixu g hg, hc.2 g hg]

end Norm

section Reduce

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

private theorem inf_eq_bot_or_le_of_simple_d36 {G : Type*} [Group G] {L P K : Subgroup G}
    (hL : IsSimpleGroup ↥L) (hLP : L ≤ P) (hK : ∀ y ∈ P, ∀ k ∈ K, y * k * y⁻¹ ∈ K) :
    K ⊓ L = ⊥ ∨ L ≤ K := by
  have : ((K ⊓ L).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨hK g (hLP g.2) n hn.1, L.mul_mem (L.mul_mem g.2 n.2) (L.inv_mem g.2)⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ L).subgroupOf L) with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact h.eq_bot_of_le inf_le_right
  · right
    rw [Subgroup.subgroupOf_eq_top] at h
    exact h.trans inf_le_left

theorem d36_reduce_of_simple (h35 : D35) (hL38 : D3L38) (std : D3Std M Mp T L V)
    (hlt : V < orbSup T V) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (hLsimp : IsSimpleGroup ↥L) :
    D36Norm M Mp T L V t ∨ D36Norm M Mp T (conjAutSub t L) V t⁻¹ := by
  obtain ⟨-, hcomm, -, -⟩ := hL38 W M Mp T L V std t ht htn hMp
  have hLMp : L ≤ Mp := by
    rw [hMp]
    exact le_sup_left
  have hLtMp : conjAutSub t L ≤ Mp := by
    rw [hMp]
    exact le_sup_right
  have hVinv : ∀ g ∈ Mp, ∀ v ∈ V, g v ∈ V := fun g hg v hv => std.hyp.irr.2.1 ⟨g, hg⟩ v hv
  have hnotCentral : ¬ ∀ g ∈ Mp, (∀ v ∈ V, g v = v) → ∀ x ∈ Mp, g * x = x * g := by
    intro hc
    have hMpL : Mp = L := (h35 W M Mp T L V std hlt hc).1
    have hle : conjAutSub t L ≤ L := hMpL ▸ hLtMp
    have hcard : Nat.card ↥(conjAutSub t L) = Nat.card ↥L :=
      Subgroup.card_map_of_injective (MulAut.conj t).injective
    have hEq : conjAutSub t L = L := Subgroup.eq_of_le_of_card_ge hle hcard.ge
    exact htn (mem_normalizer_of_conjAutSub_eq_d36 hEq)
  push Not at hnotCentral
  obtain ⟨g, hgMp, hgV, x, hxMp, hgx⟩ := hnotCentral
  set K : Subgroup (MulAut W) := Mp ⊓ centSub V
  have hgK : g ∈ K := Subgroup.mem_inf.mpr ⟨hgMp, mem_centSub.mpr hgV⟩
  have hKnorm : ∀ y ∈ Mp, ∀ k ∈ K, y * k * y⁻¹ ∈ K := by
    intro y hy k hk
    obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.mp hk
    have hk3 := mem_centSub.mp hk2
    have hmem : y * k * y⁻¹ ∈ Mp := mul_mem (mul_mem hy hk1) (inv_mem hy)
    refine Subgroup.mem_inf.mpr ⟨hmem, mem_centSub.mpr fun v hv => ?_⟩
    have h1 : y⁻¹ v ∈ V := hVinv y⁻¹ (inv_mem hy) v hv
    calc (y * k * y⁻¹) v = y (k (y⁻¹ v)) := by simp [MulAut.mul_apply]
      _ = v := by rw [hk3 _ h1]; simp
  have hLtsimp : IsSimpleGroup ↥(conjAutSub t L) :=
    (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
      ).symm.isSimpleGroup
  have hdL := inf_eq_bot_or_le_of_simple_d36 hLsimp hLMp hKnorm
  have hdLt := inf_eq_bot_or_le_of_simple_d36 hLtsimp hLtMp hKnorm
  have hcommLLt : ∀ a ∈ L, ∀ b ∈ conjAutSub t L, a * b = b * a := by
    intro a ha b hb
    exact ((Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm ha)) b hb).symm
  have hMpNL : Mp ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
    rw [hMp]
    refine sup_le Subgroup.le_normalizer fun b hb => ?_
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun a ha => hcommLLt a ha b hb)
  have hMpNLt :
      Mp ≤ Subgroup.normalizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) := by
    rw [hMp]
    refine sup_le (fun a ha => ?_) Subgroup.le_normalizer
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hcommLLt a ha b hb).symm)
  have central : ∀ P : Subgroup (MulAut W), K ⊓ P = ⊥ →
      Mp ≤ Subgroup.normalizer (P : Set (MulAut W)) → P ≤ Mp → ∀ y ∈ P, g * y = y * g := by
    intro P hP hN hPMp y hy
    have h1 : g * y * g⁻¹ * y⁻¹ ∈ K ⊓ P := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have e : g * y * g⁻¹ * y⁻¹ = g * (y * g⁻¹ * y⁻¹) := by group
        rw [e]
        exact mul_mem hgK (hKnorm y (hPMp hy) g⁻¹ (inv_mem hgK))
      · have hgy : g * y * g⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hN hgMp) y).mp hy
        exact mul_mem hgy (inv_mem hy)
    rw [hP, Subgroup.mem_bot] at h1
    calc g * y = (g * y * g⁻¹ * y⁻¹) * (y * g) := by group
      _ = y * g := by rw [h1, one_mul]
  rcases hdLt with hLt0 | hLtK
  · rcases hdL with hL0 | hLK
    · exfalso
      apply hgx
      have hLle : L ≤ Subgroup.centralizer ({g} : Set (MulAut W)) := fun y hy =>
        Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact central L hL0 hMpNL hLMp y hy
      have hLtle : conjAutSub t L ≤ Subgroup.centralizer ({g} : Set (MulAut W)) := fun y hy =>
        Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact central (conjAutSub t L) hLt0 hMpNLt hLtMp y hy
      have hMple : Mp ≤ Subgroup.centralizer ({g} : Set (MulAut W)) := by
        rw [hMp]
        exact sup_le hLle hLtle
      exact Subgroup.mem_centralizer_iff.mp (hMple hxMp) g (Set.mem_singleton g)
    · refine Or.inr ⟨⟨std.hyp.conj ht, std.qhat, std.irrT⟩, hlt, T.inv_mem ht,
        not_mem_normalizer_conjAutSub htn, ?_, ?_⟩
      · rw [conjAutSub_inv_conjAutSub, sup_comm]
        exact hMp
      · intro v hv g' hg'
        rw [conjAutSub_inv_conjAutSub] at hg'
        exact mem_centSub.mp (Subgroup.mem_inf.mp (hLK hg')).2 v hv
  · exact Or.inl ⟨std, hlt, ht, htn, hMp, fun v hv g' hg' =>
      mem_centSub.mp (Subgroup.mem_inf.mp (hLtK hg')).2 v hv⟩

theorem d36_reduce (h35 : D35) (hL38 : D3L38) (std : D3Std M Mp T L V)
    (hlt : V < orbSup T V) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) :
    D36Norm M Mp T L V t ∨ D36Norm M Mp T (conjAutSub t L) V t⁻¹ :=
  d36_reduce_of_simple h35 hL38 std hlt ht htn hMp
    (CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types
      (hL38 W M Mp T L V std t ht htn hMp).1)

end Reduce

end CFSG.Quasithin
