module

public import CFSG.Quasithin.H13.L32NLem1445b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace L1445

variable {G : Type} [Group G]

theorem conj_pow_injective {y u : G} (hy : orderOf y = 7) (hyu : y * u * y⁻¹ ≠ u) :
    Function.Injective (fun i : Fin 7 => y ^ (i : ℕ) * u * (y ^ (i : ℕ))⁻¹) := by
  have key : ∀ d : ℕ, 0 < d → d < 7 → y ^ d * u * (y ^ d)⁻¹ = u → False := by
    intro d hd0 hd7 hd
    have hc : Commute (y ^ d) u := by
      show y ^ d * u = u * y ^ d
      calc y ^ d * u = y ^ d * u * (y ^ d)⁻¹ * y ^ d := by group
        _ = u * y ^ d := by rw [hd]
    have hc' : Commute ((y ^ d) ^ (d ^ 5)) u := hc.pow_left _
    have hy1 : (y ^ d) ^ (d ^ 5) = y := by
      rw [← pow_mul, ← pow_mod_orderOf, hy]
      have : d * d ^ 5 % 7 = 1 := by interval_cases d <;> norm_num
      rw [this, pow_one]
    rw [hy1] at hc'
    exact hyu (by rw [hc'.eq, mul_inv_cancel_right])
  have step : ∀ i j : Fin 7, (i : ℕ) < j →
      y ^ (i : ℕ) * u * (y ^ (i : ℕ))⁻¹ = y ^ (j : ℕ) * u * (y ^ (j : ℕ))⁻¹ → False := by
    intro i j hij h
    obtain ⟨d, hd⟩ : ∃ d, (j : ℕ) = i + d := ⟨j - i, by omega⟩
    rw [hd, pow_add] at h
    refine key d (by omega) (by omega) ?_
    calc y ^ d * u * (y ^ d)⁻¹
        = (y ^ (i : ℕ))⁻¹ * (y ^ (i : ℕ) * y ^ d * u * (y ^ (i : ℕ) * y ^ d)⁻¹) * y ^ (i : ℕ) := by
          group
      _ = (y ^ (i : ℕ))⁻¹ * (y ^ (i : ℕ) * u * (y ^ (i : ℕ))⁻¹) * y ^ (i : ℕ) := by rw [← h]
      _ = u := by group
  intro i j h
  simp only at h
  rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
  · exact (step i j hij h).elim
  · exact Fin.ext hij
  · exact (step j i hij h.symm).elim

theorem false_of_nine {V : Subgroup G} [Finite V] (hV : Nat.card V = 8) {f : Fin 7 → G}
    (hf : Function.Injective f) (hfV : ∀ i, f i ∈ V) {a b : G} (ha : a ∈ V) (hb : b ∈ V)
    (hab : a ≠ b) (hfa : ∀ i, f i ≠ a) (hfb : ∀ i, f i ≠ b) : False := by
  let g : Fin 7 ⊕ Bool → V :=
    Sum.elim (fun i => ⟨f i, hfV i⟩) (fun t => if t then ⟨b, hb⟩ else ⟨a, ha⟩)
  have hg : Function.Injective g := by
    rintro (i | _ | _) (j | _ | _) h <;>
      simp only [g, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, ite_false, ite_true,
        Subtype.mk.injEq] at h
    · exact congrArg Sum.inl (hf h)
    · exact (hfa i h).elim
    · exact (hfb i h).elim
    · exact (hfa j h.symm).elim
    · rfl
    · exact (hab h).elim
    · exact (hfb j h.symm).elim
    · exact (hab h.symm).elim
    · rfl
  have := Nat.card_le_card_of_injective g hg
  rw [hV, Nat.card_sum] at this
  simp at this

theorem eq_one_of_fix {V : Subgroup G} [Finite V] (hV : Nat.card V = 8) {y : G}
    (hy : orderOf y = 7) (hyV : y ∈ Subgroup.normalizer (V : Set G)) {u : G} (hu : u ∈ V)
    (hyu : y * u * y⁻¹ ≠ u) {v : G} (hv : v ∈ V) (hyv : y * v * y⁻¹ = v) : v = 1 := by
  by_contra hv1
  have hcv : ∀ i : ℕ, y ^ i * v * (y ^ i)⁻¹ = v := by
    have hc : Commute y v := by
      show y * v = v * y
      calc y * v = y * v * y⁻¹ * y := by group
        _ = v * y := by rw [hyv]
    intro i
    rw [(hc.pow_left i).eq, mul_inv_cancel_right]
  refine false_of_nine hV (conj_pow_injective hy hyu)
    (fun i => (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).pow_mem hyV _) u).mp hu)
    V.one_mem hv (Ne.symm hv1) (fun i h => hyu ?_) (fun i h => hyu ?_)
  · have : u = 1 := by
      calc u = (y ^ (i : ℕ))⁻¹ * (y ^ (i : ℕ) * u * (y ^ (i : ℕ))⁻¹) * y ^ (i : ℕ) := by group
        _ = 1 := by rw [h]; group
    rw [this]; group
  · have : u = v := by
      calc u = (y ^ (i : ℕ))⁻¹ * (y ^ (i : ℕ) * u * (y ^ (i : ℕ))⁻¹) * y ^ (i : ℕ) := by group
        _ = (y ^ (i : ℕ))⁻¹ * (y ^ (i : ℕ) * v * (y ^ (i : ℕ))⁻¹) * y ^ (i : ℕ) := by
          rw [h, hcv]
        _ = v := by group
    rw [this, hyv]

theorem exists_pow_conj_eq {V : Subgroup G} [Finite V] (hV : Nat.card V = 8) {y : G}
    (hy : orderOf y = 7) (hyV : y ∈ Subgroup.normalizer (V : Set G))
    (hfix : ∀ v ∈ V, y * v * y⁻¹ = v → v = 1) {u w : G} (hu : u ∈ V) (hu1 : u ≠ 1)
    (hw : w ∈ V) (hw1 : w ≠ 1) : ∃ i : ℕ, y ^ i * u * (y ^ i)⁻¹ = w := by
  by_contra hne
  push Not at hne
  have hyu : y * u * y⁻¹ ≠ u := fun h => hu1 (hfix u hu h)
  refine false_of_nine hV (conj_pow_injective hy hyu)
    (fun i => (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).pow_mem hyV _) u).mp hu)
    V.one_mem hw (Ne.symm hw1) (fun i h => hu1 ?_) (fun i => hne i)
  calc u = (y ^ (i : ℕ))⁻¹ * (y ^ (i : ℕ) * u * (y ^ (i : ℕ))⁻¹) * y ^ (i : ℕ) := by group
    _ = 1 := by rw [h]; group

theorem exists_fix_mul {V : Subgroup G} [Finite V] {y s : G}
    (hyV : y ∈ Subgroup.normalizer (V : Set G)) (hfix : ∀ v ∈ V, y * v * y⁻¹ = v → v = 1)
    (hs : s ∈ Subgroup.centralizer (V : Set G)) (hd : y * s * y⁻¹ * s⁻¹ ∈ V) :
    ∃ w ∈ V, y * (s * w) * y⁻¹ = s * w := by
  have hconj : ∀ w ∈ V, y * w * y⁻¹ ∈ V := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hyV w).mp hw
  let φ : V → V := fun w => ⟨y * w * y⁻¹ * (w : G)⁻¹, V.mul_mem (hconj _ w.2) (V.inv_mem w.2)⟩
  have hinj : Function.Injective φ := by
    intro w w' h
    have h' : y * (w : G) * y⁻¹ * (w : G)⁻¹ = y * (w' : G) * y⁻¹ * (w' : G)⁻¹ :=
      congrArg Subtype.val h
    have hmem : (w' : G)⁻¹ * w ∈ V := V.mul_mem (V.inv_mem w'.2) w.2
    have hfx : y * ((w' : G)⁻¹ * w) * y⁻¹ = (w' : G)⁻¹ * w := by
      calc y * ((w' : G)⁻¹ * w) * y⁻¹
          = (y * (w' : G) * y⁻¹)⁻¹ * (y * (w : G) * y⁻¹ * (w : G)⁻¹) * w := by group
        _ = (y * (w' : G) * y⁻¹)⁻¹ * (y * (w' : G) * y⁻¹ * (w' : G)⁻¹) * w := by rw [h']
        _ = (w' : G)⁻¹ * w := by group
    have h1 := hfix _ hmem hfx
    apply Subtype.ext
    calc (w : G) = w' * ((w' : G)⁻¹ * w) := by group
      _ = w' := by rw [h1, mul_one]
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp hinj)
    ⟨(y * s * y⁻¹ * s⁻¹)⁻¹, V.inv_mem hd⟩
  have hw' : y * (w : G) * y⁻¹ * (w : G)⁻¹ = (y * s * y⁻¹ * s⁻¹)⁻¹ := congrArg Subtype.val hw
  refine ⟨w, w.2, ?_⟩
  have hsd : s * (y * s * y⁻¹ * s⁻¹) = (y * s * y⁻¹ * s⁻¹) * s :=
    (Subgroup.mem_centralizer_iff.mp hs _ hd).symm
  calc y * (s * w) * y⁻¹ = (y * s * y⁻¹ * s⁻¹) * s * (y * (w : G) * y⁻¹) := by group
    _ = s * (y * s * y⁻¹ * s⁻¹) * (y * (w : G) * y⁻¹) := by rw [hsd]
    _ = s * (y * s * y⁻¹ * s⁻¹) * ((y * s * y⁻¹ * s⁻¹)⁻¹ * w) := by
      rw [show y * (w : G) * y⁻¹ = (y * (w : G) * y⁻¹ * (w : G)⁻¹) * w by group, hw']
    _ = s * w := by group

theorem card_eq_mul_card_inf_centralizer {L V : Subgroup G} {s : G}
    (hmem : ∀ l ∈ L, s⁻¹ * (l * s * l⁻¹) ∈ V)
    (hsurj : ∀ w ∈ V, ∃ l ∈ L, l * s * l⁻¹ = s * w) :
    Nat.card L = Nat.card V * Nat.card ↥(L ⊓ Subgroup.centralizer ({s} : Set G)) := by
  classical
  choose σ hσL hσ using fun w : V => hsurj w w.2
  have hcent : ∀ l : L, (σ ⟨s⁻¹ * (l * s * (l : G)⁻¹), hmem l l.2⟩)⁻¹ * l ∈
      L ⊓ Subgroup.centralizer ({s} : Set G) := by
    intro l
    set w : V := ⟨s⁻¹ * (l * s * (l : G)⁻¹), hmem l l.2⟩ with hw
    refine ⟨L.mul_mem (L.inv_mem (hσL w)) l.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : σ w * s * (σ w)⁻¹ = l * s * (l : G)⁻¹ := by rw [hσ w, hw]; group
    calc (σ w)⁻¹ * l * s = (σ w)⁻¹ * (l * s * (l : G)⁻¹) * l := by group
      _ = (σ w)⁻¹ * (σ w * s * (σ w)⁻¹) * l := by rw [h1]
      _ = s * ((σ w)⁻¹ * l) := by group
  let e : L ≃ V × ↥(L ⊓ Subgroup.centralizer ({s} : Set G)) :=
    { toFun := fun l => (⟨s⁻¹ * (l * s * (l : G)⁻¹), hmem l l.2⟩, ⟨_, hcent l⟩)
      invFun := fun p => ⟨σ p.1 * p.2, L.mul_mem (hσL p.1) p.2.2.1⟩
      left_inv := fun l => by
        apply Subtype.ext
        simp only
        group
      right_inv := fun p => by
        have hc : (p.2 : G) * s = s * p.2 :=
          Subgroup.mem_centralizer_singleton_iff.mp p.2.2.2
        have hw : (⟨s⁻¹ * (σ p.1 * p.2 * s * (σ p.1 * (p.2 : G))⁻¹),
            hmem _ (L.mul_mem (hσL p.1) p.2.2.1)⟩ : V) = p.1 := by
          apply Subtype.ext
          calc s⁻¹ * (σ p.1 * p.2 * s * (σ p.1 * (p.2 : G))⁻¹)
              = s⁻¹ * (σ p.1 * ((p.2 : G) * s) * (p.2 : G)⁻¹ * (σ p.1)⁻¹) := by group
            _ = s⁻¹ * (σ p.1 * (s * p.2) * (p.2 : G)⁻¹ * (σ p.1)⁻¹) := by rw [hc]
            _ = s⁻¹ * (σ p.1 * s * (σ p.1)⁻¹) := by group
            _ = p.1 := by rw [hσ p.1]; group
        refine Prod.ext hw (Subtype.ext ?_)
        show (σ _)⁻¹ * (σ p.1 * p.2) = p.2
        rw [hw]
        group }
  rw [Nat.card_congr e, Nat.card_prod]

theorem isSylowTwoOf_of_normalizer [Finite G] {C Z : Subgroup G} (hCZ : C ≤ Z)
    (hC : IsPGroup 2 C)
    (h : ∀ P : Subgroup G, C ≤ P → P ≤ Z → P ≤ Subgroup.normalizer (C : Set G) →
      IsPGroup 2 P → P ≤ C) : IsSylowTwoOf C Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hCS, hS⟩ := exists_isSylowTwoOf_of_le hCZ hC
  suffices hSC : S ≤ C by rwa [le_antisymm hSC hCS] at hS
  have hS2 : IsPGroup 2 ↥S := hS.isPGroup
  have : Group.IsNilpotent ↥S := hS2.isNilpotent
  have hnc := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := ↥S))
  have hHN : Subgroup.normalizer ((C.subgroupOf S : Subgroup ↥S) : Set ↥S) = C.subgroupOf S := by
    refine le_antisymm (fun x hx => ?_) Subgroup.le_normalizer
    set P := (Subgroup.normalizer ((C.subgroupOf S : Subgroup ↥S) : Set ↥S)).map S.subtype
      with hP
    have hCP : C ≤ P := fun c hc =>
      ⟨⟨c, hCS hc⟩, Subgroup.le_normalizer (Subgroup.mem_subgroupOf.2 hc), rfl⟩
    have hPS : P ≤ S := Subgroup.map_subtype_le _
    have hPN : P ≤ Subgroup.normalizer (C : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      refine Subgroup.mem_normalizer_fintype fun c hc => ?_
      have := (Subgroup.mem_normalizer_iff.mp hy ⟨c, hCS hc⟩).mp (Subgroup.mem_subgroupOf.2 hc)
      exact Subgroup.mem_subgroupOf.1 this
    have hP2 : IsPGroup 2 ↥P := (hS2.to_subgroup _).map S.subtype
    exact Subgroup.mem_subgroupOf.2 (h P hCP (hPS.trans hS.le) hPN hP2 ⟨x, hx, rfl⟩)
  have htop := hnc _ hHN
  intro x hx
  have : (⟨x, hx⟩ : ↥S) ∈ C.subgroupOf S := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.1 this

end L1445

namespace L1444

variable {G : Type} [Group G] [Finite G]

namespace Setup5

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup5 G T L V V₂ g D Q₁ Q₂)
include S

theorem exists_mem_L_conj_eq {b : G} (hb : b ∈ L ⊔ T) :
    ∃ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ = b * v * b⁻¹ := by
  obtain ⟨_, S'⟩ := S.set14
  have hbN : b ∈ Subgroup.normalizer (V : Set G) := S.normV hb
  have hmem : conjAct V ⟨b, hbN⟩ ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One S'.h1281]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hmem
  refine ⟨l, Subgroup.mem_subgroupOf.1 hlL, fun v hv => ?_⟩
  exact congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hlα

theorem mem_or_mul_mem (hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) {s : G}
    (hs : s ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (hsV : s ∉ V) {b : G}
    (hb : b ∈ L ⊔ T) : b ∈ L ∨ b * s ∈ L := by
  obtain ⟨l, hl, hlb⟩ := S.exists_mem_L_conj_eq hb
  have hc : l⁻¹ * b ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨(L ⊔ T).mul_mem ((L ⊔ T).inv_mem (Subgroup.mem_sup_left hl)) hb,
      Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    calc v * (l⁻¹ * b) = l⁻¹ * (l * v * l⁻¹) * l * (l⁻¹ * b) := by group
      _ = l⁻¹ * (b * v * b⁻¹) * l * (l⁻¹ * b) := by rw [hlb v hv]
      _ = l⁻¹ * b * v := by group
  by_cases hcV : l⁻¹ * b ∈ V
  · left
    rw [show b = l * (l⁻¹ * b) by group]
    exact L.mul_mem hl (S.V_le_L hcV)
  · right
    have h1 := S.inv_mul_mem_V hc hs hcV hsV
    have hcc : (l⁻¹ * b)⁻¹ = l⁻¹ * b := inv_eq_of_mul_eq_one_left (S.mul_self_cent hCTL hc)
    rw [hcc] at h1
    rw [show b * s = l * (l⁻¹ * b * s) by group]
    exact L.mul_mem hl (S.V_le_L h1)

theorem relIndex_T (hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) {s : G}
    (hs : s ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (hsV : s ∉ V) :
    (T ⊓ L).relIndex T = 2 := by
  rw [Subgroup.inf_relIndex_left]
  refine Subgroup.index_eq_two_iff_exists_notMem_and.mpr ⟨⟨s, S.cent_le_T hs⟩, fun h => ?_,
    fun b => ?_⟩
  · exact hsV (S.mem_V_of_mem_cent hs (Subgroup.mem_subgroupOf.1 h))
  · rcases S.mem_or_mul_mem hCTL hs hsV (Subgroup.mem_sup_right b.2) with h | h
    · exact Or.inr (Subgroup.mem_subgroupOf.2 h)
    · exact Or.inl (Subgroup.mem_subgroupOf.2 h)

theorem exists_seven :
    ∃ y ∈ L, orderOf y = 7 ∧ ∃ u ∈ V, y * u * y⁻¹ ≠ u := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 7 (by rw [S.cardL]; norm_num)
  refine ⟨y, y.2, by rw [Subgroup.orderOf_coe, hy], ?_⟩
  by_contra h
  push Not at h
  have hyV : (y : G) ∈ V := S.centL.le ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun v hv => by
    calc v * y = (y : G) * v * (y : G)⁻¹ * y := by rw [h v hv]
      _ = y * v := by group⟩
  have h2 : orderOf (y : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (S.elem.2 _ hyV)
  rw [Subgroup.orderOf_coe, hy] at h2
  norm_num at h2

theorem exists_fix_cent {y : G} (hyL : y ∈ L) (hfix : ∀ v ∈ V, y * v * y⁻¹ = v → v = 1)
    {s₀ : G} (hs₀ : s₀ ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (hs₀V : s₀ ∉ V) :
    ∃ s ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G), s ∉ V ∧ y * s * y⁻¹ = s := by
  obtain ⟨w, hw, hfx⟩ := L1445.exists_fix_mul (S.L_le_normV hyL) hfix hs₀.2
    (S.comm_mem_V_of_cent hs₀ hyL)
  have hwC : w ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
    ⟨Subgroup.mem_sup_left (S.V_le_L hw),
      Subgroup.mem_centralizer_iff.mpr fun v hv => S.comm_V hv hw⟩
  refine ⟨s₀ * w, Subgroup.mul_mem _ hs₀ hwC, fun h => hs₀V ?_, hfx⟩
  rw [show s₀ = s₀ * w * w⁻¹ by group]
  exact V.mul_mem h (V.inv_mem hw)

theorem exists_conj_cent (hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) {y : G} (hyL : y ∈ L)
    (hy : orderOf y = 7) (hfix : ∀ v ∈ V, y * v * y⁻¹ = v → v = 1) {s : G}
    (hs : s ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (hsV : s ∉ V)
    (hys : y * s * y⁻¹ = s) {w : G} (hw : w ∈ V) : ∃ l ∈ L, l * s * l⁻¹ = s * w := by
  have hsv : ∀ v ∈ V, s * v = v * s := fun v hv =>
    (Subgroup.mem_centralizer_iff.mp hs.2 v hv).symm
  obtain ⟨l₀, hl₀, hl₀s⟩ : ∃ l₀ ∈ L, l₀ * s * l₀⁻¹ ≠ s := by
    by_contra h
    push Not at h
    have h1 := L1444.Setup5.eq_one_of_comm_L hCTL (S.cent_le_T hs) h
    exact hsV (h1 ▸ V.one_mem)
  set u := l₀ * s * l₀⁻¹ * s⁻¹ with hu
  have huV : u ∈ V := S.comm_mem_V_of_cent hs hl₀
  have hu1 : u ≠ 1 := fun h => hl₀s (by
    calc l₀ * s * l₀⁻¹ = l₀ * s * l₀⁻¹ * s⁻¹ * s := by group
      _ = s := by rw [← hu, h, one_mul])
  by_cases hw1 : w = 1
  · exact ⟨1, L.one_mem, by rw [hw1]; group⟩
  obtain ⟨i, hi⟩ := L1445.exists_pow_conj_eq S.card8 hy (S.L_le_normV hyL) hfix huV hu1 hw hw1
  have hcs : ∀ j : ℕ, y ^ j * s * (y ^ j)⁻¹ = s := by
    have hc : Commute y s := by
      show y * s = s * y
      calc y * s = y * s * y⁻¹ * y := by group
        _ = s * y := by rw [hys]
    intro j
    rw [(hc.pow_left j).eq, mul_inv_cancel_right]
  refine ⟨y ^ i * l₀, L.mul_mem (L.pow_mem hyL i) hl₀, ?_⟩
  calc y ^ i * l₀ * s * (y ^ i * l₀)⁻¹ = y ^ i * (u * s) * (y ^ i)⁻¹ := by rw [hu]; group
    _ = (y ^ i * u * (y ^ i)⁻¹) * (y ^ i * s * (y ^ i)⁻¹) := by group
    _ = w * s := by rw [hi, hcs]
    _ = s * w := (hsv w hw).symm

theorem card_inf_centralizer {s : G} (hs : s ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))
    (htr : ∀ w ∈ V, ∃ l ∈ L, l * s * l⁻¹ = s * w) :
    Nat.card ↥(L ⊓ Subgroup.centralizer ({s} : Set G)) = 168 := by
  have hmem : ∀ l ∈ L, s⁻¹ * (l * s * l⁻¹) ∈ V := by
    intro l hl
    have h := S.comm_mem_V_of_cent hs hl
    have hsv := (Subgroup.mem_centralizer_iff.mp hs.2 _ h).symm
    rw [show s⁻¹ * (l * s * l⁻¹) = s⁻¹ * (l * s * l⁻¹ * s⁻¹) * s by group, mul_assoc, ← hsv]
    simpa using h
  have h := L1445.card_eq_mul_card_inf_centralizer hmem htr
  rw [S.cardL, S.card8] at h
  omega

theorem le_cent_of_isPGroup (hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) {s : G}
    (hs : s ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (hsV : s ∉ V)
    (h168 : Nat.card ↥(L ⊓ Subgroup.centralizer ({s} : Set G)) = 168) {P : Subgroup G}
    (hCP : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ P)
    (hP : P ≤ (L ⊔ T) ⊓ Subgroup.centralizer ({s} : Set G)) (hP2 : IsPGroup 2 P) :
    P ≤ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
  have hVC : V ≤ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := fun v hv =>
    ⟨Subgroup.mem_sup_left (S.V_le_L hv),
      Subgroup.mem_centralizer_iff.mpr fun w hw => S.comm_V hw hv⟩
  have hPL : P ⊓ L = V := by
    have hle : V ≤ P ⊓ L := le_inf (hVC.trans hCP) S.V_le_L
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [S.card8]
    have hdvd : Nat.card ↥(P ⊓ L) ∣ 168 := by
      rw [← h168]
      exact Subgroup.card_dvd_of_le fun x hx => ⟨hx.2, (hP hx.1).2⟩
    obtain ⟨k, hk⟩ := (hP2.to_le inf_le_left).exists_card_eq
    rw [hk] at hdvd ⊢
    have hcop : Nat.Coprime (2 ^ k) 21 := Nat.Coprime.pow_left k (by norm_num)
    have h8 : 2 ^ k ∣ 8 := hcop.dvd_of_dvd_mul_right (by simpa using hdvd)
    exact Nat.le_of_dvd (by norm_num) h8
  intro p hp
  rcases S.mem_or_mul_mem hCTL hs hsV (hP hp).1 with h | h
  · exact hVC (hPL ▸ ⟨hp, h⟩)
  · have hps : p * s ∈ V := hPL ▸ ⟨P.mul_mem hp (hCP hs), h⟩
    rw [show p = p * s * s⁻¹ by group]
    exact Subgroup.mul_mem _ (hVC hps) (Subgroup.inv_mem _ hs)

end Setup5

end L1444

end CFSG.Quasithin.H13
