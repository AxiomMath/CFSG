module

public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

theorem commutator_mul_central_left {X : Type*} [Group X] {g h z : X}
    (hz : z ∈ Subgroup.center X) : ⁅g * z, h⁆ = ⁅g, h⁆ := by
  have hz' : ∀ x : X, z * x = x * z := fun x => (Subgroup.mem_center_iff.mp hz x).symm
  have hzh : z * h * z⁻¹ = h := by rw [hz' h, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc g * z * h * (g * z)⁻¹ * h⁻¹ = g * (z * h * z⁻¹) * g⁻¹ * h⁻¹ := by group
    _ = g * h * g⁻¹ * h⁻¹ := by rw [hzh]

theorem commutator_mul_central_right {X : Type*} [Group X] {g h w : X}
    (hw : w ∈ Subgroup.center X) : ⁅g, h * w⁆ = ⁅g, h⁆ := by
  have hw' : ∀ x : X, w * x = x * w := fun x => (Subgroup.mem_center_iff.mp hw x).symm
  have hwg : w * g⁻¹ * w⁻¹ = g⁻¹ := by rw [hw' g⁻¹, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc g * (h * w) * g⁻¹ * (h * w)⁻¹ = g * h * (w * g⁻¹ * w⁻¹) * h⁻¹ := by group
    _ = g * h * g⁻¹ * h⁻¹ := by rw [hwg]

theorem normal_le_center_or_eq_top {X : Type*} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) {N : Subgroup X} (hN : N.Normal) :
    N ≤ Subgroup.center X ∨ N = ⊤ := by
  obtain ⟨hperf, hsimp, -⟩ := hX
  haveI := hsimp
  have hmap : (N.map (QuotientGroup.mk' (Subgroup.center X))).Normal :=
    hN.map (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _)
  rcases Subgroup.Normal.eq_bot_or_eq_top (N.map (QuotientGroup.mk' (Subgroup.center X))) with
    hbot | htop
  · left
    intro n hn
    have hmem : QuotientGroup.mk' (Subgroup.center X) n ∈
        N.map (QuotientGroup.mk' (Subgroup.center X)) := Subgroup.mem_map_of_mem _ hn
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center X) n).mp hmem
  · right
    have hsurj : ∀ a : X, ∃ n ∈ N, ∃ z ∈ Subgroup.center X, a = n * z := by
      intro a
      have ha : QuotientGroup.mk' (Subgroup.center X) a ∈
          N.map (QuotientGroup.mk' (Subgroup.center X)) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hna⟩ := Subgroup.mem_map.mp ha
      have hna' : (n : X ⧸ Subgroup.center X) = (a : X ⧸ Subgroup.center X) := hna
      exact ⟨n, hn, n⁻¹ * a, QuotientGroup.eq.mp hna', (mul_inv_cancel_left n a).symm⟩
    have hcomm : commutator X ≤ N := by
      apply Subgroup.commutator_le.mpr
      intro a _ b _
      obtain ⟨n, hn, z, hz, rfl⟩ := hsurj a
      obtain ⟨m, hm, w, hw, rfl⟩ := hsurj b
      rw [commutator_mul_central_left hz, commutator_mul_central_right hw, commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hn hm) (N.inv_mem hn)) (N.inv_mem hm)
    rw [Group.isPerfect_def.mp hperf] at hcomm
    exact top_le_iff.mp hcomm

theorem eq_bot_of_two_pGroup_le_center {X : Type*} [Group X] [Finite X]
    (hodd : Odd (Nat.card (Subgroup.center X))) {S : Subgroup X} (hS2 : IsPGroup 2 ↥S)
    (hSZ : S ≤ Subgroup.center X) : S = ⊥ := by
  have hdvd : Nat.card S ∣ Nat.card (Subgroup.center X) := Subgroup.card_dvd_of_le hSZ
  have hoddS : Odd (Nat.card S) := Odd.of_dvd_nat hodd hdvd
  rcases hS2.card_eq_or_dvd with h1 | h2
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    have h3 := Nat.odd_iff.mp hoddS
    omega

theorem normalClosure_eq_top_of_quasisimple {X : Type*} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) (hodd : Odd (Nat.card (Subgroup.center X)))
    {S : Subgroup X} (hS2 : IsPGroup 2 ↥S) (hS1 : S ≠ ⊥) :
    Subgroup.normalClosure (S : Set X) = ⊤ := by
  have hN : (Subgroup.normalClosure (S : Set X)).Normal := Subgroup.normalClosure_normal
  rcases normal_le_center_or_eq_top hX hN with h | h
  · exfalso
    apply hS1
    apply eq_bot_of_two_pGroup_le_center hodd hS2
    intro s hs
    exact h (Subgroup.subset_normalClosure (SetLike.mem_coe.mpr hs))
  · exact h

theorem odd_card_center_of_normal_normal {Γ : Type} [Group Γ] [Finite Γ]
    (hΓ : CFSG.pCore 2 Γ = ⊥) {H X : Subgroup Γ} (hH : H.Normal) (hXH : X ≤ H)
    (hX : (X.subgroupOf H).Normal) : Odd (Nat.card (Subgroup.center ↥X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center ↥X) := by
    rcases Nat.even_or_odd (Nat.card (Subgroup.center ↥X)) with h | h
    · exact even_iff_two_dvd.mp h
    · exact absurd h hodd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥X)) 2 h2
  have hw2 : z.1 ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz] at h
    simpa using congrArg Subtype.val h
  obtain ⟨x, hxX, hxc, hx2, hx1⟩ :
      ∃ x : Γ, x ∈ X ∧ (∀ g ∈ X, g * x = x * g) ∧ x ^ 2 = 1 ∧ x ≠ 1 := by
    refine ⟨(z.1 : Γ), z.1.2, fun g hg => ?_, ?_, ?_⟩
    · simpa using congrArg (fun t : X => (t : Γ)) (Subgroup.mem_center_iff.mp z.2 ⟨g, hg⟩)
    · simpa using congrArg (fun t : X => (t : Γ)) hw2
    · intro h
      have hz1 : z = 1 := Subtype.ext (Subtype.ext h)
      rw [hz1, orderOf_one] at hz
      omega
  obtain ⟨T, hT⟩ : ∃ T : Subgroup Γ,
      ∀ y, y ∈ T ↔ (y ∈ X ∧ (∀ g ∈ X, g * y = y * g) ∧ y ^ 2 = 1) := by
    refine ⟨{ carrier := {y | y ∈ X ∧ (∀ g ∈ X, g * y = y * g) ∧ y ^ 2 = 1},
              mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun y => Iff.rfl⟩
    · rintro a b ⟨ha, hac, ha2⟩ ⟨hb, hbc, hb2⟩
      have hc : Commute a b := hbc a ha
      change a * b ∈ X ∧ (∀ g ∈ X, g * (a * b) = a * b * g) ∧ (a * b) ^ 2 = 1
      refine ⟨X.mul_mem ha hb, fun g hg => ?_, ?_⟩
      · rw [← mul_assoc, hac g hg, mul_assoc, hbc g hg, mul_assoc]
      · rw [hc.mul_pow, ha2, hb2, one_mul]
    · change (1 : Γ) ∈ X ∧ (∀ g ∈ X, g * 1 = 1 * g) ∧ (1 : Γ) ^ 2 = 1
      exact ⟨X.one_mem, fun g _ => by simp, by simp⟩
    · rintro a ⟨ha, hac, ha2⟩
      change a⁻¹ ∈ X ∧ (∀ g ∈ X, g * a⁻¹ = a⁻¹ * g) ∧ a⁻¹ ^ 2 = 1
      refine ⟨X.inv_mem ha, fun g hg => ?_, ?_⟩
      · exact (show Commute g a from hac g hg).inv_right
      · rw [inv_pow, ha2, inv_one]
  have hTX : ∀ y ∈ T, y ∈ X := fun y hy => ((hT y).mp hy).1
  have hTH : T ≤ H := by
    intro y hy
    exact hXH (hTX y hy)
  have hxT : x ∈ T := (hT x).mpr ⟨hxX, hxc, hx2⟩
  have hconj : ∀ h ∈ H, ∀ y ∈ X, h * y * h⁻¹ ∈ X := by
    intro h hh y hy
    have hk := hX.conj_mem ⟨y, hXH hy⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨h, hh⟩
    exact Subgroup.mem_subgroupOf.mp hk
  have hconj' : ∀ h ∈ H, ∀ y ∈ X, h⁻¹ * y * h ∈ X := by
    intro h hh y hy
    have hk := hconj h⁻¹ (H.inv_mem hh) y hy
    rwa [inv_inv] at hk
  have hTconj : ∀ h ∈ H, ∀ y ∈ T, h * y * h⁻¹ ∈ T := by
    intro h hh y hy
    obtain ⟨hy, hyc, hy2⟩ := (hT y).mp hy
    refine (hT _).mpr ⟨hconj h hh y hy, fun g hg => ?_, ?_⟩
    · have hc : h⁻¹ * g * h * y = y * (h⁻¹ * g * h) := hyc _ (hconj' h hh g hg)
      calc g * (h * y * h⁻¹) = h * (h⁻¹ * g * h * y) * h⁻¹ := by group
        _ = h * (y * (h⁻¹ * g * h)) * h⁻¹ := by rw [hc]
        _ = h * y * h⁻¹ * g := by group
    · rw [conj_pow, hy2, mul_one, mul_inv_cancel]
  have hTHn : (T.subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hTconj (g : Γ) g.2 n hn
  have hTp : IsPGroup 2 ↥(T.subgroupOf H) := by
    intro g
    refine ⟨1, ?_⟩
    have hg : ((g : H) : Γ) ^ 2 = 1 := ((hT _).mp (Subgroup.mem_subgroupOf.mp g.2)).2.2
    apply Subtype.ext
    apply Subtype.ext
    simpa using hg
  have hTcore : T.subgroupOf H ≤ CFSG.pCore 2 ↥H := by
    rw [CFSG.pCore_eq_iSup 2 ↥H]
    exact le_iSup_of_le (T.subgroupOf H) (le_iSup_of_le hTHn (le_iSup_of_le hTp le_rfl))
  have hTO : T ≤ (CFSG.pCore 2 ↥H).map H.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hTH]
    exact Subgroup.map_mono hTcore
  have hOn : ((CFSG.pCore 2 ↥H).map H.subtype).Normal := inferInstance
  have hOp : IsPGroup 2 ↥((CFSG.pCore 2 ↥H).map H.subtype) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype
  have hOcore : (CFSG.pCore 2 ↥H).map H.subtype ≤ CFSG.pCore 2 Γ := by
    rw [CFSG.pCore_eq_iSup 2 Γ]
    exact le_iSup_of_le ((CFSG.pCore 2 ↥H).map H.subtype)
      (le_iSup_of_le hOn (le_iSup_of_le hOp le_rfl))
  have hxO : x ∈ CFSG.pCore 2 Γ := hOcore (hTO hxT)
  rw [hΓ, Subgroup.mem_bot] at hxO
  exact hx1 hxO

private theorem stroth80_central_one {G : Type*} [Group G] [IsSimpleGroup G]
    (hG : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : ∀ g : G, z * g = g * z) : z = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · have hzc : z ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => (hz g).symm
    rw [h, Subgroup.mem_bot] at hzc
    exact hzc
  · obtain ⟨a, b, hab⟩ := hG
    have ha : a ∈ Subgroup.center G := by
      rw [h]
      exact Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab

private theorem stroth80_exists_not_comm {G : Type*} [Group G] [IsSimpleGroup G]
    (hG : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : z ≠ 1) : ∃ g : G, z * g ≠ g * z := by
  by_contra hcon
  push Not at hcon
  exact hz (stroth80_central_one hG hcon)

private theorem stroth80_comm_ne_one {G : Type*} [Group G] {x g : G} (h : x * g ≠ g * x) :
    g * x * g⁻¹ * x⁻¹ ≠ 1 := by
  intro h1
  apply h
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm

private theorem stroth80_mem_fst_comm {A B : Type*} [Group A] [Group B]
    (N : Subgroup (A × B)) [hN : N.Normal] {a : A} {b : B} (h : ((a, b) : A × B) ∈ N)
    (g : A) :
    ((g * a * g⁻¹ * a⁻¹ : A), (1 : B)) ∈ N := by
  have h1 : ((g, (1 : B)) * (a, b) * (g, (1 : B))⁻¹ : A × B) ∈ N :=
    Subgroup.Normal.conj_mem hN _ h _
  have h2 := N.mul_mem h1 (N.inv_mem h)
  have heq : ((g * a * g⁻¹ * a⁻¹ : A), (1 : B)) =
      (g, (1 : B)) * (a, b) * (g, (1 : B))⁻¹ * (a, b)⁻¹ := by
    ext <;> simp
  rw [heq]
  exact h2

private theorem stroth80_mem_snd_comm {A B : Type*} [Group A] [Group B]
    (N : Subgroup (A × B)) [hN : N.Normal] {a : A} {b : B} (h : ((a, b) : A × B) ∈ N)
    (g : B) :
    ((1 : A), (g * b * g⁻¹ * b⁻¹ : B)) ∈ N := by
  have h1 : (((1 : A), g) * (a, b) * ((1 : A), g)⁻¹ : A × B) ∈ N :=
    Subgroup.Normal.conj_mem hN _ h _
  have h2 := N.mul_mem h1 (N.inv_mem h)
  have heq : ((1 : A), (g * b * g⁻¹ * b⁻¹ : B)) =
      ((1 : A), g) * (a, b) * ((1 : A), g)⁻¹ * (a, b)⁻¹ := by
    ext <;> simp
  rw [heq]
  exact h2

private theorem stroth80_le_fst {A B : Type*} [Group A] [Group B] [IsSimpleGroup A]
    (N : Subgroup (A × B)) [N.Normal] {c : A} (hc : c ≠ 1)
    (hmem : ((c, (1 : B)) : A × B) ∈ N) :
    (⊤ : Subgroup A).prod (⊥ : Subgroup B) ≤ N := by
  have hK : N.comap (MonoidHom.inl A B) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MonoidHom.inl A B)) with h | h
    · exfalso
      have hcK : c ∈ N.comap (MonoidHom.inl A B) := hmem
      rw [h, Subgroup.mem_bot] at hcK
      exact hc hcK
    · exact h
  intro p hp
  rw [Subgroup.mem_prod] at hp
  obtain ⟨_, hp2⟩ := hp
  have hp2' : p.2 = 1 := Subgroup.mem_bot.mp hp2
  have hpK : p.1 ∈ N.comap (MonoidHom.inl A B) := by
    rw [hK]
    exact Subgroup.mem_top _
  have hp' : ((p.1, (1 : B)) : A × B) ∈ N := hpK
  have hpe : p = (p.1, (1 : B)) := Prod.ext rfl hp2'
  rw [hpe]
  exact hp'

private theorem stroth80_le_snd {A B : Type*} [Group A] [Group B] [IsSimpleGroup B]
    (N : Subgroup (A × B)) [N.Normal] {c : B} (hc : c ≠ 1)
    (hmem : (((1 : A), c) : A × B) ∈ N) :
    (⊥ : Subgroup A).prod (⊤ : Subgroup B) ≤ N := by
  have hK : N.comap (MonoidHom.inr A B) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MonoidHom.inr A B)) with h | h
    · exfalso
      have hcK : c ∈ N.comap (MonoidHom.inr A B) := hmem
      rw [h, Subgroup.mem_bot] at hcK
      exact hc hcK
    · exact h
  intro p hp
  rw [Subgroup.mem_prod] at hp
  obtain ⟨hp1, _⟩ := hp
  have hp1' : p.1 = 1 := Subgroup.mem_bot.mp hp1
  have hpK : p.2 ∈ N.comap (MonoidHom.inr A B) := by
    rw [hK]
    exact Subgroup.mem_top _
  have hp' : (((1 : A), p.2) : A × B) ∈ N := hpK
  have hpe : p = ((1 : A), p.2) := Prod.ext hp1' rfl
  rw [hpe]
  exact hp'

private theorem stroth80_top_bot_mem {A B : Type*} [Group A] [Group B] (a : A) :
    ((a, (1 : B)) : A × B) ∈ (⊤ : Subgroup A).prod (⊥ : Subgroup B) :=
  Subgroup.mem_prod.mpr ⟨Subgroup.mem_top a, Subgroup.mem_bot.mpr rfl⟩

private theorem stroth80_bot_top_mem {A B : Type*} [Group A] [Group B] (b : B) :
    (((1 : A), b) : A × B) ∈ (⊥ : Subgroup A).prod (⊤ : Subgroup B) :=
  Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top b⟩

private theorem stroth80_le_or {A B : Type*} [Group A] [Group B] [IsSimpleGroup A]
    [IsSimpleGroup B] (hA : ∃ a b : A, a * b ≠ b * a) (hB : ∃ a b : B, a * b ≠ b * a)
    (N : Subgroup (A × B)) [N.Normal] (h : N ≠ ⊥) :
    (⊤ : Subgroup A).prod (⊥ : Subgroup B) ≤ N ∨
      (⊥ : Subgroup A).prod (⊤ : Subgroup B) ≤ N := by
  obtain ⟨⟨a, b⟩, hx, hne⟩ : ∃ x ∈ N, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact h ((Subgroup.eq_bot_iff_forall N).mpr hcon)
  by_cases ha : a = 1
  · right
    subst ha
    have hb : b ≠ 1 := by
      rintro rfl
      exact hne rfl
    obtain ⟨g, hg⟩ := stroth80_exists_not_comm hB hb
    exact stroth80_le_snd N (stroth80_comm_ne_one hg) (stroth80_mem_snd_comm N hx g)
  · left
    obtain ⟨g, hg⟩ := stroth80_exists_not_comm hA ha
    exact stroth80_le_fst N (stroth80_comm_ne_one hg) (stroth80_mem_fst_comm N hx g)

theorem commuting_normal_ne_bot_prod {A B : Type*} [Group A] [Group B] [IsSimpleGroup A]
    [IsSimpleGroup B] (hA : ∃ a b : A, a * b ≠ b * a) (hB : ∃ a b : B, a * b ≠ b * a)
    {N₁ N₂ : Subgroup (A × B)} [N₁.Normal] [N₂.Normal] (h1 : N₁ ≠ ⊥) (h2 : N₂ ≠ ⊥)
    (hc : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x) :
    (N₁ = (⊤ : Subgroup A).prod ⊥ ∧ N₂ = (⊥ : Subgroup A).prod ⊤) ∨
    (N₁ = (⊥ : Subgroup A).prod ⊤ ∧ N₂ = (⊤ : Subgroup A).prod ⊥) := by
  rcases stroth80_le_or hA hB N₁ h1 with hP1 | hQ1 <;>
    rcases stroth80_le_or hA hB N₂ h2 with hP2 | hQ2
  · exfalso
    obtain ⟨a, b, hab⟩ := hA
    have hmem1 : ((a, (1 : B)) : A × B) ∈ N₁ := hP1 (stroth80_top_bot_mem a)
    have hmem2 : ((b, (1 : B)) : A × B) ∈ N₂ := hP2 (stroth80_top_bot_mem b)
    have h := congrArg Prod.fst (hc _ hmem1 _ hmem2)
    exact hab h
  · left
    refine ⟨le_antisymm ?_ hP1, le_antisymm ?_ hQ2⟩
    · intro x hx
      rw [Subgroup.mem_prod]
      refine ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr (stroth80_central_one hB ?_)⟩
      intro g
      have hmem : ((1 : A), g) ∈ N₂ := hQ2 (stroth80_bot_top_mem g)
      have h := congrArg Prod.snd (hc x hx _ hmem)
      exact h
    · intro y hy
      rw [Subgroup.mem_prod]
      refine ⟨Subgroup.mem_bot.mpr (stroth80_central_one hA ?_), Subgroup.mem_top _⟩
      intro g
      have hmem : ((g, (1 : B)) : A × B) ∈ N₁ := hP1 (stroth80_top_bot_mem g)
      have h := congrArg Prod.fst (hc _ hmem y hy)
      exact h.symm
  · right
    refine ⟨le_antisymm ?_ hQ1, le_antisymm ?_ hP2⟩
    · intro x hx
      rw [Subgroup.mem_prod]
      refine ⟨Subgroup.mem_bot.mpr (stroth80_central_one hA ?_), Subgroup.mem_top _⟩
      intro g
      have hmem : ((g, (1 : B)) : A × B) ∈ N₂ := hP2 (stroth80_top_bot_mem g)
      have h := congrArg Prod.fst (hc x hx _ hmem)
      exact h
    · intro y hy
      rw [Subgroup.mem_prod]
      refine ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr (stroth80_central_one hB ?_)⟩
      intro g
      have hmem : ((1 : A), g) ∈ N₁ := hQ1 (stroth80_bot_top_mem g)
      have h := congrArg Prod.snd (hc _ hmem y hy)
      exact h.symm
  · exfalso
    obtain ⟨a, b, hab⟩ := hB
    have hmem1 : (((1 : A), b) : A × B) ∈ N₁ := hQ1 (stroth80_bot_top_mem b)
    have hmem2 : (((1 : A), a) : A × B) ∈ N₂ := hQ2 (stroth80_bot_top_mem a)
    have h := congrArg Prod.snd (hc _ hmem1 _ hmem2)
    exact hab h.symm

end CFSG.RankThree.GF2n.Stroth80
