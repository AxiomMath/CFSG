module

public import CFSG.Quasithin.H13.A6S1357
public import CFSG.Quasithin.H13.A5S132

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def PairHyp (a b : P6) : Prop := InW4 a ∧ InW4 b ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b

instance (a b : P6) : Decidable (PairHyp a b) := by unfold PairHyp; infer_instance

@[expose] def IsoWit (a b : P6) : Prop :=
  ∃ σ : Perm (Fin 6), (∀ y : P6, InW2 y → act4f σ y = 1 ∨ act4f σ y = a ∨ act4f σ y = b ∨
    act4f σ y = a * b) ∧ Perm.sign σ = 1

instance (a b : P6) : Decidable (IsoWit a b) := by unfold IsoWit; infer_instance

theorem isoWit : ∀ a b : P6, PairHyp a b → dot a b = 0 → IsoWit a b := by
  decide +kernel

@[expose] def NondegFixAt (a b : P6) (σ : Perm (Fin 6)) : Prop :=
  act4f σ a = a → act4f σ b = b → σ ^ 4 = 1 → Perm.sign σ = 1 → σ = 1

instance (a b : P6) (σ : Perm (Fin 6)) : Decidable (NondegFixAt a b σ) := by
  unfold NondegFixAt; infer_instance

@[expose] def NondegFix (a b : P6) : Prop := ∀ σ : Perm (Fin 6), NondegFixAt a b σ

instance (a b : P6) : Decidable (NondegFix a b) := by unfold NondegFix; infer_instance

theorem nondegFix : ∀ a b : P6, InW4 a → InW4 b → dot a b = 1 → NondegFix a b := by
  decide +kernel

theorem k0_facts : (∀ y : P6, InW2 y → act4f (swap 0 1 * swap 2 3) y = y) ∧
    swap (0 : Fin 6) 1 * swap 2 3 ≠ 1 := by
  decide +kernel

theorem zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem not_alt12_2_2 : ¬ Alt12_2_2 G := by
  intro h
  apply S.h13.not_excluded
  rcases h with ⟨t, n, f, hf, -, hadm, hLie⟩ | hU | hM | hM | hM
  · exact Or.inl ⟨t, n, f, hf, hadm, hLie⟩
  · exact Or.inl ⟨.PSU, 5, 2, le_rfl, ⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩, hU⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl hM)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hM))))))

theorem mem_normalizer_V_of_TI (h1222 : Stmt12_2_2) {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) {W : Subgroup G} (hWV : W ≤ V) (hW : W ≠ ⊥)
    (hmW : ∀ w ∈ W, m * w * m⁻¹ ∈ V) : m ∈ Subgroup.normalizer (V : Set G) := by
  rcases h1222 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow with h | h
  · exact absurd h S.not_alt12_2_2
  have hTI := ((h L S.maximal S.h13.faithful S.fsu.quasisimple).2.2 V S.irr).2.1 m hm
  have hmem : ∀ x, x ∈ CFSG.conjugate V m ↔ m * x * m⁻¹ ∈ V := by
    intro x
    unfold CFSG.conjugate
    rw [Subgroup.mem_map_equiv]
    simp
  rcases hTI with h1 | h1
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [← hmem, h1]
  · exfalso
    apply hW
    rw [eq_bot_iff, ← h1]
    exact fun w hw => ⟨hWV hw, (hmem w).2 (hmW w hw)⟩

theorem exists_odd_T {m : ↥(Subgroup.normalizer (V : Set G))}
    (hm : Perm.sign (S.frame.ρ m) ≠ 1) :
    ∃ t : ↥(Subgroup.normalizer (V : Set G)), (t : G) ∈ T ∧ Perm.sign (S.frame.ρ t) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  let φ : ↥(Subgroup.normalizer (V : Set G)) →* ℤˣ := Perm.sign.comp S.frame.ρ
  have hTk : T.subgroupOf (Subgroup.normalizer (V : Set G)) ≤ φ.ker := fun t ht => hcon t ht
  have hsurj : Function.Surjective φ := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one φ⟩
    · refine ⟨m, ?_⟩
      rcases Int.units_eq_one_or (φ m) with h | h
      · exact absurd h hm
      · exact h
  have hidx : φ.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hsyl := A5.isSylowTwoOf_of_le S.h13.sylow S.frame.T_le
  apply hsyl.2.2
  rw [← hidx]
  exact Subgroup.index_dvd_of_le hTk

theorem sign_rho_eq_one (hA : autOn T V ≤ autOn L V)
    (m : ↥(Subgroup.normalizer (V : Set G))) : Perm.sign (S.frame.ρ m) = 1 := by
  by_contra hm
  obtain ⟨t, htT, ht⟩ := S.exists_odd_T hm
  obtain ⟨x, hxL, hx⟩ := hA ⟨t, htT, rfl⟩
  apply ht
  rw [← S.rho_eq_of_conjAct_eq hx]
  exact Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨x, hxL, rfl⟩)

theorem isSylowTwoOf_CTV :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G)) (Subgroup.centralizer (V : Set G)) :=
  A4.isSylowTwoOf_inf_normal (A5.isSylowTwoOf_of_le S.h13.sylow S.frame.T_le)
    (Subgroup.centralizer_le_normalizer (V : Set G))
    (A5.normalizer_le_normalizer_centralizer' V)

theorem normalizer_CTV_le :
    Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  rw [S.cT]
  have hVQ : V ≤ pCoreOf 2 (L ⊔ T) := by
    rw [← S.cT]
    refine le_inf S.V_le_T fun v hv => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val (S.elemAbelian_V.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)
  have hne : pCoreOf 2 (L ⊔ T) ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff] at hVQ
    have := S.card_V
    rw [hVQ, Subgroup.card_bot] at this
    omega
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G)) :=
    ⟨_, hne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have := S.uniqueM.2 M' ⟨hM', (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans hle⟩
  exact this ▸ hle

theorem card_CTV_lt :
    Nat.card ↥(T ⊓ Subgroup.centralizer (V : Set G)) <
      Nat.card ↥(T ⊓ Subgroup.centralizer (S.V2 : Set G)) := by
  have hle : T ⊓ Subgroup.centralizer (V : Set G) ≤ T ⊓ Subgroup.centralizer (S.V2 : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le S.V2_le_V)
  obtain ⟨t, htT, ht⟩ := S.frame.DA_T _ gens_DA.1.1 gens_DA.1.2
  have htV2 : (t : G) ∈ Subgroup.centralizer (S.V2 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨hwV, hwW2⟩ := S.mem_pre.1 hw
    have h : act4 (S.frame.ρ t) (S.frame.ψ ⟨w, hwV⟩) = S.frame.ψ ⟨w, hwV⟩ := by
      rw [ht]
      exact Subtype.ext (k0_facts.1 _ hwW2)
    have := (S.conj_eq_iff t ⟨w, hwV⟩).2 h
    calc w * t = t * w * (t : G)⁻¹ * t := by rw [this]
      _ = t * w := by group
  have htV : (t : G) ∉ Subgroup.centralizer (V : Set G) := fun h => by
    have := (S.rho_eq_one_iff t).2 h
    rw [ht] at this
    exact k0_facts.2 this
  by_contra hcon
  push Not at hcon
  have heq := Subgroup.eq_of_le_of_card_ge hle hcon
  exact htV (heq ▸ ⟨htT, htV2⟩ : (t : G) ∈ T ⊓ Subgroup.centralizer (V : Set G)).2

theorem not_nondegenerate
    (h1222 : Stmt12_2_2) (hA : autOn T V ≤ autOn L V) (g : G)
    (hW : conjSub g S.V2 ≤ V) {a b : G} (ha : a ∈ conjSub g S.V2) (hb : b ∈ conjSub g S.V2) :
    dot (S.frame.ψ ⟨a, hW ha⟩ : P6) (S.frame.ψ ⟨b, hW hb⟩ : P6) ≠ 1 := by
  intro hdot
  set W := conjSub g S.V2 with hWdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQC : Q ≤ Subgroup.centralizer (W : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le hW)
  have hQ2 : IsPGroup 2 Q := S.h13.sylow.1.to_le inf_le_left
  set P := conjSub g (T ⊓ Subgroup.centralizer (S.V2 : Set G)) with hPdef
  have hPC : P ≤ Subgroup.centralizer (W : Set G) := by
    rw [hWdef, conjSub_centralizer]
    exact conjSub_mono g inf_le_right
  have hP2 : IsPGroup 2 P := F7.isPGroup_conjSub (S.h13.sylow.1.to_le inf_le_left)
  have hQP : Nat.card Q < Nat.card P := by
    rw [hPdef, A5.card_conjSub']
    exact S.card_CTV_lt
  obtain ⟨S', hS', hQS'⟩ := A4.exists_isSylowTwoOf_ge hQC hQ2
  obtain ⟨x, -, hx⟩ := F7.isSylowTwoOf_exists_conj_le hS' hPC hP2
  have hPS' : Nat.card P ≤ Nat.card S' :=
    (Subgroup.card_le_of_le hx).trans (A5.card_conjSub' x S').le
  have hlt : Q < S' := lt_of_le_of_ne hQS' fun h => by
    rw [h] at hQP
    omega
  obtain ⟨s, hsS', hsQ, hsN⟩ := A5.exists_mem_normalizer_not_mem hS'.2.1 hlt
  have hsM : s ∈ Subgroup.normalizer (L : Set G) := S.normalizer_CTV_le hsN
  have hsC : s ∈ Subgroup.centralizer (W : Set G) := hS'.1 hsS'
  have hWne : W ≠ ⊥ := by
    rw [hWdef, Ne, conjSub_eq_bot_iff]
    intro h
    have := S.card_V2
    rw [h, Subgroup.card_bot] at this
    omega
  have hsV : s ∈ Subgroup.normalizer (V : Set G) :=
    S.mem_normalizer_V_of_TI h1222 hsM hW hWne fun w hw => by
      have := Subgroup.mem_centralizer_iff.mp hsC w hw
      rw [← this, mul_inv_cancel_right]
      exact hW hw
  have hfix : ∀ c (hc : c ∈ W), act4f (S.frame.ρ ⟨s, hsV⟩) (S.frame.ψ ⟨c, hW hc⟩ : P6) =
      (S.frame.ψ ⟨c, hW hc⟩ : P6) := by
    intro c hc
    have h := (S.conj_eq_iff ⟨s, hsV⟩ ⟨c, hW hc⟩).1 (by
      have := Subgroup.mem_centralizer_iff.mp hsC c hc
      calc s * c * s⁻¹ = c * s * s⁻¹ := by rw [this]
        _ = c := by group)
    exact congrArg Subtype.val h
  have h4 : (S.frame.ρ ⟨s, hsV⟩) ^ 4 = 1 := by
    obtain ⟨k, hk⟩ := hS'.2.1 ⟨s, hsS'⟩
    refine pow_four_of_pow_two_pow (k := k) ?_
    rw [← map_pow]
    have : (⟨s, hsV⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hρ : S.frame.ρ ⟨s, hsV⟩ = 1 :=
    nondegFix _ _ (S.frame.ψ _).2 (S.frame.ψ _).2 hdot _ (hfix a ha) (hfix b hb) h4
      (S.sign_rho_eq_one hA _)
  have hsCV := (S.rho_eq_one_iff _).1 hρ
  have heq := F1.eq_of_isSylowTwoOf_le S.isSylowTwoOf_CTV inf_le_right
    (hS'.2.1.to_le inf_le_left) (le_inf hQS' inf_le_right)
  have hmem : s ∈ S' ⊓ Subgroup.centralizer (V : Set G) := ⟨hsS', hsCV⟩
  rw [← heq] at hmem
  exact hsQ hmem

theorem lemma13_5_6_two_of_A6
    (h1222 : Stmt12_2_2) (hA : autOn T V ≤ autOn L V) (g : G)
    (hW : conjSub g S.V2 ≤ V) : ∃ l ∈ L, conjSub g S.V2 = conjSub l S.V2 := by
  classical
  set W := conjSub g S.V2 with hWdef
  have hcardW : Nat.card W = 4 := by rw [hWdef, A5.card_conjSub', S.card_V2]
  obtain ⟨a, haW, ha1⟩ : ∃ a ∈ W, a ≠ 1 := by
    by_contra h
    push Not at h
    have : W = ⊥ := (Subgroup.eq_bot_iff_forall W).2 h
    rw [this, Subgroup.card_bot] at hcardW
    omega
  obtain ⟨b, hbW, hb1, hba⟩ : ∃ b ∈ W, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hsub : (W : Set G) ⊆ {1, a} := by
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (h x hx hx1)
    have : Nat.card W ≤ 2 := by
      calc Nat.card W = Nat.card (W : Set G) := rfl
        _ ≤ Nat.card ({1, a} : Set G) := Nat.card_mono (Set.toFinite _) hsub
        _ ≤ 2 := by
          rw [Nat.card_coe_set_eq]
          exact (Set.ncard_insert_le _ _).trans (by simp)
    omega
  have hinj : ∀ (u v : ↥V), (S.frame.ψ u : P6) = (S.frame.ψ v : P6) → (u : G) = v := by
    intro u v h
    exact congrArg Subtype.val (S.frame.ψ.injective (Subtype.ext h))
  have hα1 : (S.frame.ψ ⟨a, hW haW⟩ : P6) ≠ 1 := fun h => ha1 (by
    have := hinj ⟨a, hW haW⟩ 1 (by rw [map_one]; exact h)
    simpa using this)
  have hβ1 : (S.frame.ψ ⟨b, hW hbW⟩ : P6) ≠ 1 := fun h => hb1 (by
    have := hinj ⟨b, hW hbW⟩ 1 (by rw [map_one]; exact h)
    simpa using this)
  have hαβ : (S.frame.ψ ⟨a, hW haW⟩ : P6) ≠ (S.frame.ψ ⟨b, hW hbW⟩ : P6) := fun h =>
    hba (hinj _ _ h).symm
  rcases zmod2_cases (dot (S.frame.ψ ⟨a, hW haW⟩ : P6) (S.frame.ψ ⟨b, hW hbW⟩ : P6)) with hd | hd
  ·
    obtain ⟨σ, hσW, hσs⟩ := isoWit _ _ ⟨(S.frame.ψ _).2, (S.frame.ψ _).2, hα1, hβ1, hαβ⟩ hd
    obtain ⟨l, hlL, hl⟩ := (S.frame.image_L σ).2 (Perm.mem_alternatingGroup.2 hσs)
    refine ⟨l, hlL, (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm⟩
    · intro x hx
      rw [mem_conjSub] at hx
      obtain ⟨hyV, hyW2⟩ := S.mem_pre.1 hx
      have hxy : x = l * ((l : G)⁻¹ * x * l) * (l : G)⁻¹ := by group
      have hxV : x ∈ V := by
        rw [hxy]
        exact (Subgroup.mem_normalizer_iff.mp l.2 _).mp hyV
      have hψ : (S.frame.ψ ⟨x, hxV⟩ : P6) =
          act4f σ (S.frame.ψ ⟨(l : G)⁻¹ * x * l, hyV⟩ : P6) := by
        have h1 := S.psi_conj l ⟨(l : G)⁻¹ * x * l, hyV⟩
        rw [hl] at h1
        have e : (⟨x, hxV⟩ : ↥V) = ⟨l * ((l : G)⁻¹ * x * l) * (l : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp l.2 _).mp hyV⟩ := Subtype.ext hxy
        rw [e, h1]
        rfl
      rcases hσW _ hyW2 with h | h | h | h <;> rw [← hψ] at h
      · have hx1 : x = ((1 : ↥V) : G) := hinj ⟨x, hxV⟩ 1 (by rw [map_one]; exact h)
        rw [hx1]
        exact W.one_mem
      · have hxa : x = a := hinj ⟨x, hxV⟩ ⟨a, hW haW⟩ h
        rw [hxa]
        exact haW
      · have hxb : x = b := hinj ⟨x, hxV⟩ ⟨b, hW hbW⟩ h
        rw [hxb]
        exact hbW
      · have hxab : x = a * b :=
          hinj ⟨x, hxV⟩ (⟨a, hW haW⟩ * ⟨b, hW hbW⟩) (by rw [map_mul]; exact h)
        rw [hxab]
        exact W.mul_mem haW hbW
    · rw [hcardW, A5.card_conjSub', S.card_V2]
  · exact absurd hd (S.not_nondegenerate h1222 hA g hW haW hbW)

end Setting4

@[expose] def Input1356TwoS6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ autOn T V ≤ autOn L V → ∀ g : G, conjSub g S.V2 ≤ V →
      ∃ l ∈ L, conjSub g S.V2 = conjSub l S.V2

theorem input1356Two_of
    (h1222 : Stmt12_2_2) (hS6 : Input1356TwoS6) : Input1356Two := by
  intro G _ _ T L V S hNS g hW
  by_cases hA : autOn T V ≤ autOn L V
  · exact S.lemma13_5_6_two_of_A6 h1222 hA g hW
  · exact hS6 G T L V S hNS hA g hW

end CFSG.Quasithin.H13.A6
