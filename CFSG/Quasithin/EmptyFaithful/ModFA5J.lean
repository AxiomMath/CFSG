module

public import CFSG.Quasithin.EmptyFaithful.ModFA5Cfg
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCOffender
public import CFSG.Quasithin.EmptyFaithful.S1469Inputs

public section

namespace CFSG.Quasithin.ModF

open scoped Pointwise commutatorElement
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2 CFSG.LieType.BorelTits
  Equiv

variable {G : Type} [Group G] [Finite G] {I S Iz K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_sup {g : G} {X Y : Subgroup G} (hX : g ∈ Subgroup.normalizer (X : Set G))
    (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  refine B6.mem_normalizer_of_conjSub_le ?_ ?_
  · rw [OrderIso.map_sup, B6.conjSub_eq_self hX, B6.conjSub_eq_self hY]
  · rw [OrderIso.map_sup, B6.conjSub_eq_self (Subgroup.inv_mem _ hX),
      B6.conjSub_eq_self (Subgroup.inv_mem _ hY)]

namespace A5Cfg

variable (c : A5Cfg I S Iz K₁ K₂)
include c

omit [Finite G] in
theorem S_le_normalizer_sup : S ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
  intro t ht
  refine B6.mem_normalizer_of_conjSub_le ?_ ?_
  · rw [OrderIso.map_sup]
    refine sup_le ?_ ?_
    · rcases c.perm₁ t ht with h | h <;> rw [h]
      · exact le_sup_left
      · exact le_sup_right
    · rcases c.perm₂ t ht with h | h <;> rw [h]
      · exact le_sup_left
      · exact le_sup_right
  · rw [OrderIso.map_sup]
    have ht' := S.inv_mem ht
    refine sup_le ?_ ?_
    · rcases c.perm₁ _ ht' with h | h <;> rw [h]
      · exact le_sup_left
      · exact le_sup_right
    · rcases c.perm₂ _ ht' with h | h <;> rw [h]
      · exact le_sup_left
      · exact le_sup_right

omit [Finite G] in
theorem I_le_normalizer_Q₀ :
    I ≤ Subgroup.normalizer ((pCoreOf 2 K₁ ⊔ pCoreOf 2 K₂ : Subgroup G) : Set G) := by
  rw [c.gen]
  refine sup_le ?_ (sup_le ?_ ?_)
  · intro t ht
    refine B6.mem_normalizer_of_conjSub_le ?_ ?_
    · rw [OrderIso.map_sup]
      refine sup_le ?_ ?_
      · have := pCoreOf_map_equiv 2 (MulAut.conj t) K₁
        show B6.conjSub t (pCoreOf 2 K₁) ≤ _
        change (pCoreOf 2 K₁).map (MulAut.conj t).toMonoidHom ≤ _
        rw [← this]
        rcases c.perm₁ t ht with h | h <;> (change pCoreOf 2 (B6.conjSub t K₁) ≤ _; rw [h])
        · exact le_sup_left
        · exact le_sup_right
      · have := pCoreOf_map_equiv 2 (MulAut.conj t) K₂
        change (pCoreOf 2 K₂).map (MulAut.conj t).toMonoidHom ≤ _
        rw [← this]
        rcases c.perm₂ t ht with h | h <;> (change pCoreOf 2 (B6.conjSub t K₂) ≤ _; rw [h])
        · exact le_sup_left
        · exact le_sup_right
    · rw [OrderIso.map_sup]
      have ht' := S.inv_mem ht
      refine sup_le ?_ ?_
      · have := pCoreOf_map_equiv 2 (MulAut.conj t⁻¹) K₁
        change (pCoreOf 2 K₁).map (MulAut.conj t⁻¹).toMonoidHom ≤ _
        rw [← this]
        rcases c.perm₁ _ ht' with h | h <;> (change pCoreOf 2 (B6.conjSub t⁻¹ K₁) ≤ _; rw [h])
        · exact le_sup_left
        · exact le_sup_right
      · have := pCoreOf_map_equiv 2 (MulAut.conj t⁻¹) K₂
        change (pCoreOf 2 K₂).map (MulAut.conj t⁻¹).toMonoidHom ≤ _
        rw [← this]
        rcases c.perm₂ _ ht' with h | h <;> (change pCoreOf 2 (B6.conjSub t⁻¹ K₂) ≤ _; rw [h])
        · exact le_sup_left
        · exact le_sup_right
  · intro k hk
    refine mem_normalizer_sup (le_normalizer_pCoreOf 2 K₁ hk) ?_
    exact Lin2.le_normalizer_of_commute (A := pCoreOf 2 K₂) (B := K₁)
      (fun p hp a ha => (c.comm a ha p (pCoreOf_le 2 K₂ hp)).symm) hk
  · intro k hk
    refine mem_normalizer_sup ?_ (le_normalizer_pCoreOf 2 K₂ hk)
    exact Lin2.le_normalizer_of_commute (A := pCoreOf 2 K₁) (B := K₂)
      (fun p hp a ha => (c.comm p (pCoreOf_le 2 K₁ hp) a ha)) hk

theorem Q₀_le_R : pCoreOf 2 K₁ ⊔ pCoreOf 2 K₂ ≤ pCoreOf 2 Iz := by
  have hQ₂ : IsPGroup 2 (pCoreOf 2 K₁ ⊔ pCoreOf 2 K₂ : Subgroup G) :=
    (pCoreOf_isPGroup 2 K₁).to_sup_of_normal_right' (pCoreOf_isPGroup 2 K₂)
      (Lin2.le_normalizer_of_commute (A := pCoreOf 2 K₂) (B := pCoreOf 2 K₁)
        (fun p hp a ha => (c.comm a (pCoreOf_le 2 K₁ ha) p (pCoreOf_le 2 K₂ hp)).symm))
  refine le_pCoreOf_of_le_normalizer 2 ?_ (c.Iz_le_I.trans c.I_le_normalizer_Q₀) hQ₂
  exact (sup_le (c.pCore_le₁.trans inf_le_left) (c.symm.pCore_le₁.trans inf_le_left)).trans c.S_le_Iz

theorem Q_le_R : pCoreOf 2 I ≤ pCoreOf 2 Iz :=
  le_pCoreOf_of_le_normalizer 2 (c.sylow.pCoreOf_le.trans c.S_le_Iz)
    (c.Iz_le_I.trans (le_normalizer_pCoreOf 2 I)) (pCoreOf_isPGroup 2 I)

theorem blockU₁_le_R : blockU K₁ ≤ pCoreOf 2 Iz :=
  (C1.blockU_le_blockQ c.blk₁.1).trans (le_sup_left.trans c.Q₀_le_R)

theorem comm_mem_pCore₁ {a : G} (haN : a ∈ Subgroup.normalizer (K₁ : Set G))
    (hU : ∀ u ∈ blockU K₁, a * u * a⁻¹ = u) {k : G} (hk : k ∈ K₁) :
    k * a * k⁻¹ * a⁻¹ ∈ pCoreOf 2 K₁ := by
  obtain ⟨α, hα, hαk, -⟩ := c.a5₁
  obtain ⟨P, -⟩ := AppC.exists_a5pi c.blk₁.1 c.a5₁ α hα hαk
  have hak : a * k * a⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.mp haN k).mp hk
  have hw : a * k * a⁻¹ * k⁻¹ ∈ K₁ := K₁.mul_mem hak (K₁.inv_mem hk)
  have hU' : ∀ u ∈ blockU K₁, a⁻¹ * u * a = u := by
    intro u hu
    calc a⁻¹ * u * a = a⁻¹ * (a * u * a⁻¹) * a := by rw [hU u hu]
      _ = u := by group
  have hwU : ∀ u ∈ blockU K₁, (a * k * a⁻¹ * k⁻¹) * u * (a * k * a⁻¹ * k⁻¹)⁻¹ = u := by
    intro u hu
    have hu' : k⁻¹ * u * k ∈ blockU K₁ := by
      have h1 := C1.mem_normalizer_blockU (L := K₁) (Subgroup.le_normalizer (K₁.inv_mem hk))
      simpa using (Subgroup.mem_normalizer_iff.mp h1 u).mp hu
    have e1 : (a * k * a⁻¹ * k⁻¹) * u * (a * k * a⁻¹ * k⁻¹)⁻¹ =
        a * k * (a⁻¹ * (k⁻¹ * u * k) * a) * k⁻¹ * a⁻¹ := by group
    rw [e1, hU' _ hu']
    have e2 : a * k * (k⁻¹ * u * k) * k⁻¹ * a⁻¹ = a * u * a⁻¹ := by group
    rw [e2, hU u hu]
  have hπ1 : P.π ⟨a * k * a⁻¹ * k⁻¹, Subgroup.le_normalizer hw⟩ = 1 :=
    (P.hker _).mpr hwU
  rw [P.hπα _ hw] at hπ1
  have hα1 : P.α ⟨_, hw⟩ = 1 := Subtype.ext hπ1
  have hmem : (⟨_, hw⟩ : ↥K₁) ∈ CFSG.pCore 2 ↥K₁ := by rw [← P.hαk]; exact hα1
  have hQ : a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 K₁ := (AppC.mem_pCore_iff_mem_blockQ _).mp hmem
  have := (pCoreOf 2 K₁).inv_mem hQ
  simpa [mul_assoc] using this

theorem centralizes_blockU₁ {A : Subgroup G} (hA : IsMaxElemAbelian (pCoreOf 2 Iz) A) :
    ∀ a ∈ A, ∀ u ∈ blockU K₁, a * u * a⁻¹ = u := by
  obtain ⟨α, hα, hαk, -⟩ := c.a5₁
  obtain ⟨P, -⟩ := AppC.exists_a5pi c.blk₁.1 c.a5₁ α hα hαk
  have hRN := c.R_le_normalizer₁
  have hAR : A ≤ pCoreOf 2 Iz := hA.1
  have hU : IsElemAbelian 2 (blockU K₁) := AppC.isElemAbelian_blockU c.blk₁.1
  have hswap := P.toPiData.swapGen_im hU c.blockU₁_le_R hRN hA
  have hR2 : IsPGroup 2 (pCoreOf 2 Iz) := pCoreOf_isPGroup 2 Iz
  have hnormR := le_normalizer_pCoreOf 2 Iz
  have hno : ∀ s ∈ P.toPiData.im A, ¬ s.IsSwap := by
    intro s hs hsw
    obtain ⟨y, hyA, rfl⟩ := (P.toPiData.mem_im).mp hs
    obtain ⟨i, j, hij, hsij⟩ := hsw
    obtain ⟨c₀, hc₀N, hγ3, hγ1, hc3, hc1⟩ :=
      exists_normalizing_lift (α := P.α) P.hα (c.ker_le₁ P.hαk) c.sylow₁ hij
    have hc₀Iz : (c₀ : G) ∈ Iz := c.normalizer_le_Iz₁ P.hα P.hαk _ c₀.2 hc₀N
    have hy : (y : G) ∈ pCoreOf 2 Iz := hAR hyA
    have h1 : (c₀ : G) * y * (c₀ : G)⁻¹ ∈ pCoreOf 2 Iz :=
      (Subgroup.mem_normalizer_iff.mp (hnormR hc₀Iz) y).mp hy
    have hxR : ((c₀ : G) * y * (c₀ : G)⁻¹) * (y : G)⁻¹ ∈ pCoreOf 2 Iz :=
      (pCoreOf 2 Iz).mul_mem h1 ((pCoreOf 2 Iz).inv_mem hy)
    let yc : ↥(Subgroup.normalizer (K₁ : Set G)) := ⟨c₀, Subgroup.le_normalizer c₀.2⟩
    have hπc : P.π yc = toPerm P.α c₀ := P.hπα c₀ c₀.2
    obtain ⟨n, hn⟩ := hR2 ⟨_, hxR⟩
    have hxn : (yc * y * yc⁻¹ * y⁻¹) ^ (2 ^ n) = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hn
    have hπx : P.π (yc * y * yc⁻¹ * y⁻¹) =
        toPerm P.α c₀ * swap i j * (toPerm P.α c₀)⁻¹ * swap i j := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπc, hsij, swap_inv]
    have h2 : (P.π (yc * y * yc⁻¹ * y⁻¹)) ^ (2 ^ n) = 1 := by
      rw [← map_pow, hxn, map_one]
    rw [hπx] at h2
    have hg : (toPerm P.α c₀ * swap i j * (toPerm P.α c₀)⁻¹ * swap i j) ^ (Nat.gcd (2 ^ n) 3) = 1 :=
      pow_gcd_eq_one.mpr ⟨h2, hc3⟩
    have hcop : Nat.gcd (2 ^ n) 3 = 1 := Nat.Coprime.pow_left n (by norm_num)
    rw [hcop, pow_one] at hg
    exact hc1 hg
  have hbot : P.toPiData.im A = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
    have hmem := hswap g hg
    have hempty : {s : Perm (Fin 5) | s ∈ P.toPiData.im A ∧ s.IsSwap} = ∅ := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun ⟨h1, h2⟩ => hno s h1 h2
    rw [hempty, Subgroup.closure_empty, Subgroup.mem_bot] at hmem
    exact hmem
  intro a ha u hu
  have hmem : P.π ⟨a, hRN (hAR ha)⟩ ∈ P.toPiData.im A := P.toPiData.pi_mem_im (K := A) ha
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (P.hker _).mp hmem u hu

theorem mem_pCoreOf_of_mem_A {A : Subgroup G} (hA : IsMaxElemAbelian (pCoreOf 2 Iz) A) :
    ∀ a ∈ A, a ∈ pCoreOf 2 I := by
  intro a ha
  have haR : a ∈ pCoreOf 2 Iz := hA.1 ha
  have haS : a ∈ S := c.R_le_S haR
  have haI : a ∈ I := c.sylow.le haS
  have hU₁ := c.centralizes_blockU₁ hA a ha
  have hU₂ := c.symm.centralizes_blockU₁ hA a ha
  refine mem_pCoreOf_of_conj_mem c.sylow.isPGroup haI fun x hx => ?_
  have hx' : x ∈ ((S : Subgroup G) : Set G) * ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right S (K₁ ⊔ K₂) c.S_le_normalizer_sup, ← c.gen]
    exact hx
  obtain ⟨s, hs, k, hk, rfl⟩ := hx'
  have hk' : k ∈ ((K₁ : Subgroup G) : Set G) * ((K₂ : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ c.K₁_le_normalizer₂]
    exact hk
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hk'
  have q₁ := c.comm_mem_pCore₁ (c.R_le_normalizer₁ haR) hU₁ hk₁
  have q₂ := c.symm.comm_mem_pCore₁ (c.R_le_normalizer₂ haR) hU₂ hk₂
  have hq₂K : k₂ * a * k₂⁻¹ * a⁻¹ ∈ K₂ := pCoreOf_le 2 K₂ q₂
  have hcomm : k₁ * (k₂ * a * k₂⁻¹ * a⁻¹) = (k₂ * a * k₂⁻¹ * a⁻¹) * k₁ := c.comm k₁ hk₁ _ hq₂K
  have e : s * (k₁ * k₂) * a * (s * (k₁ * k₂))⁻¹ =
      s * ((k₂ * a * k₂⁻¹ * a⁻¹) * (k₁ * a * k₁⁻¹ * a⁻¹) * a) * s⁻¹ := by
    have h1 : s * (k₁ * k₂) * a * (s * (k₁ * k₂))⁻¹ =
        s * (k₁ * ((k₂ * a * k₂⁻¹ * a⁻¹) * a) * k₁⁻¹) * s⁻¹ := by group
    rw [h1]
    have h2 : k₁ * ((k₂ * a * k₂⁻¹ * a⁻¹) * a) * k₁⁻¹ =
        (k₁ * (k₂ * a * k₂⁻¹ * a⁻¹) * k₁⁻¹) * (k₁ * a * k₁⁻¹) := by group
    rw [h2]
    have h3 : k₁ * (k₂ * a * k₂⁻¹ * a⁻¹) * k₁⁻¹ = k₂ * a * k₂⁻¹ * a⁻¹ := by
      rw [hcomm]; group
    rw [h3]
    group
  rw [e]
  have hq₁S : k₁ * a * k₁⁻¹ * a⁻¹ ∈ S := (c.pCore_le₁ q₁).1
  have hq₂S : k₂ * a * k₂⁻¹ * a⁻¹ ∈ S := (c.symm.pCore_le₁ q₂).1
  exact S.mul_mem (S.mul_mem hs (S.mul_mem (S.mul_mem hq₂S hq₁S) haS)) (S.inv_mem hs)

end A5Cfg

omit [Finite G] in
theorem A5Cfg.of_blockProduct (hmin : MinParabolic I S Iz) (hblk : IsBlockProduct I S 2 ![K₁, K₂])
    (h₁ : IsAltType K₁ 5) (h₂ : IsAltType K₂ 5) : A5Cfg I S Iz K₁ K₂ := by
  obtain ⟨-, -, hb, hcomm, hres, -, hinv⟩ := hblk
  have h01 : ⁅K₁, K₂⁆ = ⊥ := by simpa using hcomm 0 1 (by decide)
  refine ⟨hmin, (hb 0).1, (hb 1).1, h₁, h₂, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb'
    have h1 : ⁅a, b⁆ ∈ ⁅K₁, K₂⁆ := Subgroup.commutator_mem_commutator ha hb'
    rw [h01, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  · intro t ht
    obtain ⟨j, hj⟩ := hinv t ht 0
    fin_cases j
    · exact Or.inl (by simpa using hj)
    · exact Or.inr (by simpa using hj)
  · intro t ht
    obtain ⟨j, hj⟩ := hinv t ht 1
    fin_cases j
    · exact Or.inl (by simpa using hj)
    · exact Or.inr (by simpa using hj)
  · have hsup : (⨆ i, (![K₁, K₂] : Fin 2 → Subgroup G) i) = K₁ ⊔ K₂ :=
      le_antisymm (iSup_le fun i => by fin_cases i <;> simp)
        (sup_le (le_iSup (![K₁, K₂] : Fin 2 → Subgroup G) 0)
          (le_iSup (![K₁, K₂] : Fin 2 → Subgroup G) 1))
    rw [← hsup]
    exact hres

theorem pRank_pos_of_card {E R : Subgroup G} (hER : E ≤ R) (hE : IsElemAbelian 2 E)
    (hn : 2 ≤ Nat.card E) : 0 < CFSG.Open.pRank 2 R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero] at hk
    omega
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup G, E ≤ R ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨E, _, _, hk⟩
    calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
      _ = Nat.card E := hk.symm
      _ ≤ Nat.card G := E.card_le_card_group
  have hle : k ≤ CFSG.Open.pRank 2 R := le_csSup hbdd ⟨E, hER, hE, hk⟩
  omega

end CFSG.Quasithin.ModF

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.ModF

theorem input1469A5J_proved : Input1469A5J := by
  intro G _ _ I S Iz K₁ K₂ _ _ hmin hblk h5₁ h5₂ _
  have c : A5Cfg I S Iz K₁ K₂ := A5Cfg.of_blockProduct hmin hblk h5₁ h5₂
  have hJQ : thompsonJ (pCoreOf 2 Iz) ≤ pCoreOf 2 I :=
    iSup_le fun A => iSup_le fun hA a ha => c.mem_pCoreOf_of_mem_A hA a ha
  obtain ⟨α, hα, hαk, -⟩ := c.a5₁
  obtain ⟨P, -⟩ := AppC.exists_a5pi c.blk₁.1 c.a5₁ α hα hαk
  have hU : IsElemAbelian 2 (blockU K₁) := AppC.isElemAbelian_blockU c.blk₁.1
  have hcard : Nat.card (blockU K₁) = 16 := P.toPiData.card_blockU
  have h0 : 0 < CFSG.Open.pRank 2 (pCoreOf 2 Iz) :=
    pRank_pos_of_card c.blockU₁_le_R hU (by rw [hcard]; norm_num)
  have h := thompsonJi_eq_of_le h0 (by rw [← thompsonJ_eq_thompsonJi_zero]; exact hJQ) c.Q_le_R
  rw [← thompsonJ_eq_thompsonJi_zero, ← thompsonJ_eq_thompsonJi_zero] at h
  exact h

end CFSG.Quasithin
