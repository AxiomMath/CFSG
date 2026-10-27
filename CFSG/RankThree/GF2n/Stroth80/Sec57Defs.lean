module

public import CFSG.RankThree.GF2n.Smith81.Sec117
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def CaseA (Q Z : Subgroup G) (t : G) : Prop := ∃ z ∈ Z, ∀ y ∈ Q, y * t * y⁻¹ ≠ t * z

@[expose] def RootTrans (M Q Z B : Subgroup G) : Prop :=
  ∀ X : Subgroup G, Ctx M Q Z X → ∃ m ∈ M, conjSubgroup m B = X

@[expose] def Stroth57AllStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → (∀ B' : Subgroup G, Ctx M Q Z B' → NoA2 Q Z (LB M Q B')) →
    SLNat hc t → (∃ g : G, ∃ b ∈ B, g * t * g⁻¹ = b) → B ≤ QB (Subgroup.zpowers t) →
      Vt M (LB M Q B) B Z t ≤ (Q ⊓ QB (Subgroup.zpowers t)) ⊔ Z

theorem genByB_of_CQt (hc : Ctx M Q Z B) (hgen : GenByB M Q B) (h5 :
    CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G))
    {B' : Subgroup G} (hc' : Ctx M Q Z B') : GenByB M Q B' := by
  classical
  have H := hc.hyp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 hm) z).mp hz
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hQM : Q ≤ M := H.Q_normal.1
  set Q' : Subgroup G := ⨆ (m : G) (_ : m ∈ M), conjSubgroup m B' with hQ'
  have hQ'Q : Q' ≤ Q := iSup₂_le fun m hm => (hc'.conj_of_mem hm).le
  have hQ'n : ∀ m₀ ∈ M, ∀ x ∈ Q', m₀ * x * m₀⁻¹ ∈ Q' := by
    intro m₀ hm₀ x hx
    have hle : Q' ≤ Q'.comap (MulAut.conj m₀).toMonoidHom := by
      refine iSup₂_le fun m hm y hy => ?_
      rw [Subgroup.mem_comap]
      show m₀ * y * m₀⁻¹ ∈ Q'
      refine le_iSup₂_of_le (f := fun (m : G) (_ : m ∈ M) => conjSubgroup m B') (m₀ * m)
        (M.mul_mem hm₀ hm) le_rfl ?_
      rw [mem_conjSubgroup] at hy ⊢
      rw [show (m₀ * m)⁻¹ * (m₀ * y * m₀⁻¹) * (m₀ * m) = m⁻¹ * y * m by group]
      exact hy
    exact hle hx
  set N : Subgroup G := Q' ⊔ Z with hN
  have hNQ : N ≤ Q := sup_le hQ'Q hZQ
  have hNn : ∀ m₀ ∈ M, ∀ x ∈ N, m₀ * x * m₀⁻¹ ∈ N := by
    intro m₀ hm₀ x hx
    have hle : N ≤ N.comap (MulAut.conj m₀).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_comap]
        exact (le_sup_left : Q' ≤ N) (hQ'n m₀ hm₀ y hy)
      · rw [Subgroup.mem_comap]
        exact (le_sup_right : Z ≤ N) (hZn m₀ hm₀ y hy)
    exact hle hx
  set L : Subgroup G := LB M Q B with hL
  have hL2 : IsPGroup 2 L := Smith81.Sec117.isPGroup_LB hc
  have hLM : L ≤ M := fun l hl => hc.LB_le_M hl
  let f : ↥L → ↥N → ↥N := fun l x => ⟨l * x * (l : G)⁻¹, hNn l (hLM l.2) x x.2⟩
  have hf : ∀ (l : ↥L) (a b : ↥N), a⁻¹ * b ∈ Z.subgroupOf N →
      (f l a)⁻¹ * f l b ∈ Z.subgroupOf N := by
    intro l a b hab
    rw [Subgroup.mem_subgroupOf] at hab ⊢
    have : ((f l a)⁻¹ * f l b : ↥N) = (l : G) * ((a : G)⁻¹ * b) * (l : G)⁻¹ := by
      simp only [f, Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [this]
    exact hZn l (hLM l.2) _ (by simpa using hab)
  letI act : MulAction ↥L (↥N ⧸ Z.subgroupOf N) :=
    { smul := fun l => Quotient.map' (f l) (fun a b hab => by
        rw [QuotientGroup.leftRel_apply] at hab ⊢; exact hf l a b hab)
      one_smul := fun q => by
        induction q using QuotientGroup.induction_on with
        | H x => exact congrArg _ (Subtype.ext (by simp [f]))
      mul_smul := fun l₁ l₂ q => by
        induction q using QuotientGroup.induction_on with
        | H x => exact congrArg _ (Subtype.ext (by simp only [f, Subgroup.coe_mul]; group)) }
  have hsmul : ∀ (l : ↥L) (x : ↥N),
      (l • (x : ↥N ⧸ Z.subgroupOf N)) = ((f l x : ↥N) : ↥N ⧸ Z.subgroupOf N) :=
    fun l x => rfl
  have hmod := hL2.card_modEq_card_fixedPoints (↥N ⧸ Z.subgroupOf N)
  have hN2 : IsPGroup 2 N := (Smith81.Sec117.isPGroup_Q' H).to_le hNQ
  have hidx : 2 ∣ Nat.card (↥N ⧸ Z.subgroupOf N) := by
    rw [← Subgroup.index]
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    have hdvd : (Z.subgroupOf N).index ∣ 2 ^ k := hk ▸ Subgroup.index_dvd_card _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases j with _ | j
    · exfalso
      rw [pow_zero, Subgroup.index_eq_one] at hj
      obtain ⟨g', hg'⟩ := hc'.conj
      have hB'N : B' ≤ N := fun x hx => (le_sup_left : Q' ≤ N)
        (le_iSup₂_of_le (f := fun (m : G) (_ : m ∈ M) => conjSubgroup m B') 1 M.one_mem le_rfl
          (by rw [mem_conjSubgroup]; simpa using hx))
      have hB'Z : B' ≤ Z := fun x hx => by
        have : (⟨x, hB'N hx⟩ : ↥N) ∈ Z.subgroupOf N := hj ▸ Subgroup.mem_top _
        simpa [Subgroup.mem_subgroupOf] using this
      obtain ⟨z, hz, hz1⟩ := Smith81.Sec117.exists_ne_one_Z H
      apply hc'.ne
      rw [hg'] at hB'Z ⊢
      have hzg : g' * z * g'⁻¹ ∈ conjSubgroup g' Z := by
        rw [mem_conjSubgroup, show g'⁻¹ * (g' * z * g'⁻¹) * g' = z by group]; exact hz
      have hzg1 : g' * z * g'⁻¹ ≠ 1 := fun h => hz1 (by
        have := congrArg (fun y => g'⁻¹ * y * g') h; simpa [mul_assoc] using this)
      have h1 : g' * z * g'⁻¹ ∈ conjSubgroup 1 Z := by
        rw [mem_conjSubgroup]; simpa using hB'Z hzg
      rw [Smith81.conjSubgroup_eq_of_mem_ne_one H hzg1 hzg h1]
      ext y; simp [mem_conjSubgroup]
    · rw [hj, pow_succ]; exact dvd_mul_left _ _
  have hfix2 : 2 ∣ Nat.card (MulAction.fixedPoints ↥L (↥N ⧸ Z.subgroupOf N)) :=
    (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hidx)))
  have h1fix :
      ((1 : ↥N) : ↥N ⧸ Z.subgroupOf N) ∈ MulAction.fixedPoints ↥L (↥N ⧸ Z.subgroupOf N) := by
    intro l
    rw [hsmul]
    exact congrArg _ (Subtype.ext (by simp [f]))
  obtain ⟨q, hqfix, hq1⟩ : ∃ q ∈ MulAction.fixedPoints ↥L (↥N ⧸ Z.subgroupOf N),
      q ≠ ((1 : ↥N) : ↥N ⧸ Z.subgroupOf N) := by
    by_contra hcon
    push_neg at hcon
    have hsub : (MulAction.fixedPoints ↥L (↥N ⧸ Z.subgroupOf N)).Subsingleton :=
      fun a ha b hb => (hcon a ha).trans (hcon b hb).symm
    have hcard : Nat.card (MulAction.fixedPoints ↥L (↥N ⧸ Z.subgroupOf N)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨hsub.coe_sort, ⟨⟨_, h1fix⟩⟩⟩
    omega
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  have hyZ : (y : G) ∉ Z := fun h => hq1 (by
    rw [QuotientGroup.eq]; simpa [Subgroup.mem_subgroupOf] using h)
  have hyC : (y : G) ∈ CQt Q Z L := by
    refine ⟨hNQ y.2, fun l hl => ?_⟩
    have h := hqfix ⟨l, hl⟩
    rw [hsmul, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    have hw : ((f ⟨l, hl⟩ y)⁻¹ * y : ↥N) = l * (y : G)⁻¹ * l⁻¹ * y := by
      simp only [f, Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [hw] at h
    have := hZn y (hQM (hNQ y.2)) _ (Z.inv_mem h)
    rw [show (y : G) * (l * (y : G)⁻¹ * l⁻¹ * y)⁻¹ * (y : G)⁻¹ = ⁅l, (y : G)⁆ by
      rw [commutatorElement_def]; group] at this
    exact this
  rw [hL, h5] at hyC
  have hBN : B ≤ N := by
    intro b hb
    by_cases hb1 : b = 1
    · rw [hb1]; exact N.one_mem
    obtain ⟨m, hm, hmb⟩ := Smith81.Sec117.exists_conj_of_mem_sup hc hb hb1 hyC hyZ
    have := hNn m⁻¹ (M.inv_mem hm) y y.2
    rwa [← hmb, show m⁻¹ * (m * b * m⁻¹) * m⁻¹⁻¹ = b by group] at this
  have hQN : Q ≤ N := by
    rw [hgen]
    refine iSup₂_le fun m hm x hx => ?_
    rw [mem_conjSubgroup] at hx
    have := hNn m hm _ (hBN hx)
    rwa [show m * (m⁻¹ * x * m) * m⁻¹ = x by group] at this
  have hdec : ((Q' ⊔ Z : Subgroup G) : Set G) = (Q' : Set G) * (Z : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Q' Z (fun u hu => H.Z_normal.2 (hQM (hQ'Q hu)))
  obtain ⟨g, hg⟩ := hc.conj
  obtain ⟨z₀, hz₀, hz₀1⟩ := Smith81.Sec117.exists_ne_one_Z H
  set a : G := g * z₀ * g⁻¹ with ha
  have haB : a ∈ B := by
    rw [hg, mem_conjSubgroup, ha, show g⁻¹ * (g * z₀ * g⁻¹) * g = z₀ by group]; exact hz₀
  have ha1 : a ≠ 1 := fun h => hz₀1 (by
    have := congrArg (fun y => g⁻¹ * y * g) h; simpa [ha, mul_assoc] using this)
  have haZ : a ∉ Z := by
    intro haZ
    apply hc.ne
    have h1 : a ∈ conjSubgroup 1 Z := by rw [mem_conjSubgroup]; simpa using haZ
    have h2 : a ∈ conjSubgroup g Z := hg ▸ haB
    rw [hg, Smith81.conjSubgroup_eq_of_mem_ne_one H ha1 h2 h1]
    ext y; simp [mem_conjSubgroup]
  have haQ : a ∈ Q := hc.le haB
  clear_value a
  obtain ⟨c, hcQ, hca⟩ : ∃ c ∈ Q, c * a ≠ a * c := by
    by_contra hcon
    push_neg at hcon
    apply haZ
    rw [H.hZ, cen_eq]
    exact Subgroup.mem_inf.mpr ⟨haQ, Subgroup.mem_centralizer_iff.mpr fun c hc => (hcon c hc)⟩
  have hmemQ'Z : ∀ x ∈ Q, ∃ x' ∈ Q', ∃ z ∈ Z, x' * z = x := fun x hx => by
    have : x ∈ (Q' : Set G) * (Z : Set G) := by rw [← hdec]; exact hQN hx
    obtain ⟨x', hx', z, hz, rfl⟩ := Set.mem_mul.mp this
    exact ⟨x', hx', z, hz, rfl⟩
  obtain ⟨a', ha', z₁, hz₁, rfl⟩ := hmemQ'Z a haQ
  obtain ⟨c', hc', z₂, hz₂, rfl⟩ := hmemQ'Z c hcQ
  have ha'Q := hQ'Q ha'
  have hc'Q := hQ'Q hc'
  have hcomm : ⁅a' * z₁, c' * z₂⁆ = ⁅a', c'⁆ := by
    have e1 := Smith81.Z_central H hz₁ hc'Q
    have e2 := Smith81.Z_central H hz₂ ha'Q
    have e3 := Smith81.Z_central H hz₁ (hZQ hz₂)
    simp only [commutatorElement_def, mul_inv_rev]
    calc a' * z₁ * (c' * z₂) * (z₁⁻¹ * a'⁻¹) * (z₂⁻¹ * c'⁻¹)
        = a' * (z₁ * c') * z₂ * z₁⁻¹ * a'⁻¹ * z₂⁻¹ * c'⁻¹ := by group
      _ = a' * c' * a'⁻¹ * c'⁻¹ := by
        rw [e1]
        have e4 : z₂ * a'⁻¹ = a'⁻¹ * z₂ := by
          have := Smith81.Z_central H hz₂ (Q.inv_mem ha'Q); exact this
        have e5 : z₁ * a'⁻¹ = a'⁻¹ * z₁ := Smith81.Z_central H hz₁ (Q.inv_mem ha'Q)
        calc a' * (c' * z₁) * z₂ * z₁⁻¹ * a'⁻¹ * z₂⁻¹ * c'⁻¹
            = a' * c' * (z₁ * z₂ * z₁⁻¹) * a'⁻¹ * z₂⁻¹ * c'⁻¹ := by group
          _ = a' * c' * z₂ * a'⁻¹ * z₂⁻¹ * c'⁻¹ := by
            rw [show z₁ * z₂ * z₁⁻¹ = z₂ by rw [e3]; group]
          _ = a' * c' * a'⁻¹ * c'⁻¹ := by rw [mul_assoc (a' * c') z₂, e4]; group
  have hk1 : ⁅a', c'⁆ ≠ 1 := by
    rw [← hcomm]; intro h
    exact hca (by rw [commutatorElement_eq_one_iff_mul_comm] at h; exact h.symm)
  have hkZ : ⁅a', c'⁆ ∈ Z := Smith81.comm_mem_Z H ha'Q hc'Q
  have hkQ' : ⁅a', c'⁆ ∈ Q' := by
    rw [commutatorElement_def]
    exact Q'.mul_mem (Q'.mul_mem (Q'.mul_mem ha' hc') (Q'.inv_mem ha')) (Q'.inv_mem hc')
  have hZQ' : Z ≤ Q' := by
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]; exact Q'.one_mem
    obtain ⟨m, hm, hmz⟩ := Smith81.Z_isConj H hkZ hk1 hz hz1
    rw [← hmz]; exact hQ'n m hm _ hkQ'
  show Q = Q'
  exact le_antisymm (hQN.trans (sup_le le_rfl hZQ')) hQ'Q

theorem rootTrans_of_all (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (h : Sec5Hyp hc n t) (hall : ∀ B' : Subgroup G, Ctx M Q Z B' → NoA2 Q Z (LB M Q B')) :
    RootTrans M Q Z B := by
  intro X hX
  have hw := h.width
  have hn := h.n_gt
  have H := hc.hyp
  have h5B := (stroth_3_5 h34 hc hw hn h.noA2 h.gen).2.1
  have h5all : ∀ B' : Subgroup G, Ctx M Q Z B' →
      CQt Q Z (LB M Q B') = ((B' ⊔ Z : Subgroup G) : Set G) := fun B' hc' =>
    (stroth_3_5 h34 hc' hw hn (hall B' hc') (genByB_of_CQt hc h.gen h5B hc')).2.1
  obtain ⟨g, hg⟩ := hc.conj
  obtain ⟨g', hg'⟩ := hX.conj
  have hZne : Z ≠ ⊥ := by
    intro hZ
    have := H.q4
    rw [hZ, Subgroup.card_bot] at this
    omega
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZne
  have hzZ : (z : G) ∈ Z := z.2
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hmem : ∀ k : G, k * (z : G) * k⁻¹ ∈ conjSubgroup k Z := fun k => by
    rw [mem_conjSubgroup, show k⁻¹ * (k * (z : G) * k⁻¹) * k = z by group]; exact hzZ
  have hne : ∀ k : G, k * (z : G) * k⁻¹ ≠ 1 := fun k hk => hz1' (by
    have := congrArg (fun y => k⁻¹ * y * k) hk; simpa [mul_assoc] using this)
  have hnotZ : ∀ k : G, conjSubgroup k Z ≠ Z → k * (z : G) * k⁻¹ ∉ Z := fun k hk hZ => hk (by
    have h1 : k * (z : G) * k⁻¹ ∈ conjSubgroup 1 Z := by
      rw [mem_conjSubgroup]; simpa using hZ
    rw [CFSG.RankThree.GF2n.Smith81.conjSubgroup_eq_of_mem_ne_one H (hne k) (hmem k) h1]
    ext y; simp [mem_conjSubgroup])
  have hbB : g * (z : G) * g⁻¹ ∈ B := hg ▸ hmem g
  have hxX : g' * (z : G) * g'⁻¹ ∈ X := hg' ▸ hmem g'
  obtain ⟨m, hmM, hm⟩ := CFSG.RankThree.GF2n.Smith81.smith117Statement_holds G M Q Z B hc n hw
    (by omega) hall h5all _ (hc.le hbB) (hnotZ g (hg ▸ hc.ne)) _ (hX.le hxX)
    (hnotZ g' (hg' ▸ hX.ne)) (g' * g⁻¹) (by group)
  refine ⟨m, hmM, ?_⟩
  rw [hg, ← conjSubgroup_mul, hg']
  refine CFSG.RankThree.GF2n.Smith81.conjSubgroup_eq_of_mem_ne_one H (hne g') ?_ (hmem g')
  rw [← hm, show m * (g * (z : G) * g⁻¹) * m⁻¹ = (m * g) * (z : G) * (m * g)⁻¹ by group]
  exact hmem (m * g)

end CFSG.RankThree.GF2n.Stroth80
