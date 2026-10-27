module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCore
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJInner
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec17.Item1722ProofHJ

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Equiv

namespace Wales1411W.HJProd

section Prod

variable {A B : Type*} [Group A] [Group B]

theorem fst_eq_one_of_commute (hA : Function.Injective (MulAut.conj : A →* MulAut A))
    {x : A × B} (hx : ∀ a : A, ((a, 1) : A × B) * x = x * (a, 1)) : x.1 = 1 := by
  apply hA
  rw [map_one]
  ext a
  have h := congrArg Prod.fst (hx a)
  simp only [Prod.fst_mul] at h
  simp only [MulAut.conj_apply, MulAut.one_apply]
  rw [← h, mul_inv_cancel_right]

theorem prod_conj_injective (hA : Function.Injective (MulAut.conj : A →* MulAut A))
    (hB : Function.Injective (MulAut.conj : B →* MulAut B)) :
    Function.Injective (MulAut.conj : A × B →* MulAut (A × B)) := by
  intro x y h
  have h' : ∀ z : A × B, x * z * x⁻¹ = y * z * y⁻¹ := fun z => by
    have := congrArg (fun α : MulAut (A × B) => α z) h
    simpa only [MulAut.conj_apply] using this
  refine Prod.ext (hA ?_) (hB ?_)
  · ext a
    have := congrArg Prod.fst (h' (a, 1))
    simpa only [MulAut.conj_apply, Prod.fst_mul, Prod.fst_inv] using this
  · ext b
    have := congrArg Prod.snd (h' (1, b))
    simpa only [MulAut.conj_apply, Prod.snd_mul, Prod.snd_inv] using this

theorem card_ker_snd [Finite A] [Finite B] : Nat.card (MonoidHom.snd A B).ker = Nat.card A := by
  have h := Subgroup.card_ker_mul_card_range (MonoidHom.snd A B)
  rw [(MonoidHom.snd A B).range_eq_top_of_surjective (fun b => ⟨(1, b), rfl⟩),
    Subgroup.card_top, Nat.card_prod] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

theorem snd_eq_one_of_aut [Finite A] [Finite B] [IsSimpleGroup B]
    (hAB : Nat.card A < Nat.card B) (β : MulAut (A × B)) {x : A × B} (hx : x.2 = 1) :
    (β x).2 = 1 := by
  set N := (MonoidHom.snd A B).ker.map β.toMonoidHom with hN
  have hNn : N.Normal := (MonoidHom.normal_ker _).map _ β.surjective
  set K := N.map (MonoidHom.snd A B) with hK
  have hKn : K.Normal := hNn.map _ fun b => ⟨(1, b), rfl⟩
  rcases (haveI := hKn; Subgroup.Normal.eq_bot_or_eq_top K) with h | h
  · have hmem : (MonoidHom.snd A B) (β x) ∈ K :=
      ⟨β x, ⟨x, (MonoidHom.mem_ker).mpr hx, rfl⟩, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  · exfalso
    have h1 : Nat.card K ≤ Nat.card N :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd N (MonoidHom.snd A B))
    have h2 : Nat.card N = Nat.card A := by
      rw [hN, Subgroup.card_map_of_injective β.injective, card_ker_snd]
    rw [h, Subgroup.card_top] at h1
    omega

theorem fst_eq_one_of_aut [Finite A] [Finite B] [IsSimpleGroup B]
    (hAB : Nat.card A < Nat.card B) (hA : Function.Injective (MulAut.conj : A →* MulAut A))
    (β : MulAut (A × B)) {x : A × B} (hx : x.1 = 1) : (β x).1 = 1 := by
  apply fst_eq_one_of_commute hA
  intro a
  set w := β.symm (a, 1) with hw
  have hw2 : w.2 = 1 := snd_eq_one_of_aut hAB β.symm rfl
  have hwx : w * x = x * w := Prod.ext (by simp [hx]) (by simp [hw2])
  have hβw : β w = (a, 1) := by rw [hw]; exact β.apply_symm_apply _
  rw [← hβw, ← map_mul, ← map_mul, hwx]

theorem mem_range_conj_of_pow_three [Finite A] [Finite B] [IsSimpleGroup B]
    (hAB : Nat.card A < Nat.card B) (hAc : Function.Injective (MulAut.conj : A →* MulAut A))
    (hA : ∀ α : MulAut A, α ^ 3 = 1 → α ∈ (MulAut.conj : A →* MulAut A).range)
    (hB : ∀ α : MulAut B, α ^ 3 = 1 → α ∈ (MulAut.conj : B →* MulAut B).range)
    (β : MulAut (A × B)) (hβ : β ^ 3 = 1) :
    β ∈ (MulAut.conj : A × B →* MulAut (A × B)).range := by
  have hβA : ∀ a : A, β (a, 1) = ((β (a, 1)).1, 1) := fun a =>
    Prod.ext rfl (snd_eq_one_of_aut hAB β rfl)
  have hβB : ∀ b : B, β (1, b) = (1, (β (1, b)).2) := fun b =>
    Prod.ext (fst_eq_one_of_aut hAB hAc β rfl) rfl
  set fA : A →* A := (MonoidHom.fst A B).comp (β.toMonoidHom.comp (MonoidHom.inl A B)) with hfA
  set fB : B →* B := (MonoidHom.snd A B).comp (β.toMonoidHom.comp (MonoidHom.inr A B)) with hfB
  have hfAi : Function.Injective fA := by
    intro a a' h
    have h1 : β (a, 1) = β (a', 1) := by
      rw [hβA a, hβA a']
      exact Prod.ext h rfl
    exact congrArg Prod.fst (β.injective h1)
  have hfBi : Function.Injective fB := by
    intro b b' h
    have h1 : β (1, b) = β (1, b') := by
      rw [hβB b, hβB b']
      exact Prod.ext rfl h
    exact congrArg Prod.snd (β.injective h1)
  set αA : MulAut A := MulEquiv.ofBijective fA (Finite.injective_iff_bijective.mp hfAi) with hαA
  set αB : MulAut B := MulEquiv.ofBijective fB (Finite.injective_iff_bijective.mp hfBi) with hαB
  have hpowA : ∀ k : ℕ, ∀ a : A, (β ^ k) (a, 1) = ((αA ^ k) a, 1) := by
    intro k
    induction k with
    | zero => intro a; rfl
    | succ k ih =>
      intro a
      rw [pow_succ', MulAut.mul_apply, ih, pow_succ', MulAut.mul_apply, hβA]
      rfl
  have hpowB : ∀ k : ℕ, ∀ b : B, (β ^ k) (1, b) = (1, (αB ^ k) b) := by
    intro k
    induction k with
    | zero => intro b; rfl
    | succ k ih =>
      intro b
      rw [pow_succ', MulAut.mul_apply, ih, pow_succ', MulAut.mul_apply, hβB]
      rfl
  have hαA3 : αA ^ 3 = 1 := by
    ext a
    have h := hpowA 3 a
    rw [hβ, MulAut.one_apply] at h
    exact (congrArg Prod.fst h).symm
  have hαB3 : αB ^ 3 = 1 := by
    ext b
    have h := hpowB 3 b
    rw [hβ, MulAut.one_apply] at h
    exact (congrArg Prod.snd h).symm
  obtain ⟨x1, hx1⟩ := hA αA hαA3
  obtain ⟨x2, hx2⟩ := hB αB hαB3
  refine ⟨(x1, x2), MulEquiv.ext fun p => ?_⟩
  obtain ⟨a, b⟩ := p
  have h1 : β (a, b) = β (a, 1) * β (1, b) := by rw [← map_mul]; simp
  have ha : (β (a, 1)).1 = x1 * a * x1⁻¹ := by
    rw [← MulAut.conj_apply, hx1]
    rfl
  have hb : (β (1, b)).2 = x2 * b * x2⁻¹ := by
    rw [← MulAut.conj_apply, hx2]
    rfl
  rw [h1, hβA, hβB, ha, hb]
  refine Prod.ext ?_ ?_ <;> simp [MulAut.conj_apply]

theorem exists_three_centralizer_not_mem [Finite A] [Finite B] (hA9 : ¬ 9 ∣ Nat.card A)
    {c0 : A} (hc0 : orderOf c0 = 3)
    (hB : ∀ d : B, orderOf d = 3 → ∃ y : B, orderOf y = 3 ∧ Commute d y ∧
      y ∉ Subgroup.zpowers d)
    (E : Subgroup (A × B)) (hcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    (h3 : ∀ e ∈ E, e ^ 3 = 1) (h9 : Nat.card E = 9) :
    ∃ y : A × B, orderOf y = 3 ∧ (∀ e ∈ E, e * y = y * e) ∧ y ∉ E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hfst : ∀ e ∈ E, e.1 = 1
  · refine ⟨(c0, 1), ?_, fun e he => ?_, fun hm => ?_⟩
    · rw [Prod.orderOf]
      simp [hc0]
    · ext <;> simp [hfst e he]
    · have h := hfst _ hm
      simp only at h
      rw [h, orderOf_one] at hc0
      norm_num at hc0
  push Not at hfst
  obtain ⟨e, he, he1⟩ := hfst
  have hc3 : e.1 ^ 3 = 1 := by
    have := congrArg Prod.fst (h3 e he)
    simpa using this
  have hco : orderOf e.1 = 3 := orderOf_eq_prime hc3 he1
  by_cases hcE : ((e.1, 1) : A × B) ∈ E
  swap
  · refine ⟨(e.1, 1), ?_, fun f hf => ?_, hcE⟩
    · rw [Prod.orderOf]
      simp [hco]
    · have h1 : e.1 * f.1 = f.1 * e.1 := by
        have := congrArg Prod.fst (hcomm e he f hf)
        simpa using this
      ext <;> simp [h1]
  set g : ↥E →* A := (MonoidHom.fst A B).comp E.subtype with hg
  have hcard := Subgroup.card_ker_mul_card_range g
  have hcmem : e.1 ∈ g.range := ⟨⟨e, he⟩, rfl⟩
  have hrange : Nat.card g.range = 3 := by
    have hd1 : Nat.card g.range ∣ 3 ^ 2 := by
      have := Subgroup.card_range_dvd g
      rwa [h9] at this
    have hd2 : Nat.card g.range ∣ Nat.card A := Subgroup.card_subgroup_dvd_card _
    have hd3 : 3 ∣ Nat.card g.range := by
      have := Subgroup.orderOf_dvd_natCard _ hcmem
      rwa [hco] at this
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd1
    interval_cases k
    · rw [hk', pow_zero] at hd3
      norm_num at hd3
    · rw [hk', pow_one]
    · rw [hk'] at hd2
      exact absurd hd2 (by norm_num; exact hA9)
  have hker : Nat.card g.ker = 3 := by
    rw [h9, hrange] at hcard
    omega
  have hrangeEq : g.range = Subgroup.zpowers e.1 :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcmem)
      (by rw [hrange, Nat.card_zpowers, hco])).symm
  have hne : g.ker ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hker
    norm_num at hker
  obtain ⟨⟨k, hkK⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hk1' : k ≠ 1 := fun h => hk1 (Subtype.ext h)
  have hkfst : (k : A × B).1 = 1 := (MonoidHom.mem_ker).mp hkK
  have hk3 : k ^ 3 = 1 := Subtype.ext (by simpa using h3 _ k.2)
  have hko : orderOf k = 3 := orderOf_eq_prime hk3 hk1'
  have hkerEq : g.ker = Subgroup.zpowers k :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hkK)
      (by rw [hker, Nat.card_zpowers, hko])).symm
  set d : B := (k : A × B).2 with hd
  have hd1 : d ≠ 1 := fun h => hk1' (Subtype.ext (Prod.ext hkfst h))
  have hd3 : d ^ 3 = 1 := by
    have := congrArg Prod.snd (h3 _ k.2)
    simpa using this
  have hdo : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hsnd : ∀ f ∈ E, f.2 ∈ Subgroup.zpowers d := by
    intro f hf
    have hf1 : f.1 ∈ g.range := ⟨⟨f, hf⟩, rfl⟩
    rw [hrangeEq] at hf1
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hf1
    have hf' : f * ((e.1, 1) : A × B) ^ (-m) ∈ E := mul_mem hf (zpow_mem hcE _)
    have hf'K : (⟨_, hf'⟩ : ↥E) ∈ g.ker := by
      rw [MonoidHom.mem_ker]
      show (f * ((e.1, 1) : A × B) ^ (-m)).1 = 1
      rw [Prod.fst_mul, Prod.pow_fst, ← hm, ← zpow_add, add_neg_cancel, zpow_zero]
    rw [hkerEq] at hf'K
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hf'K
    have h2 := congrArg (fun z : ↥E => (z : A × B).2) hn
    simp only [Subgroup.coe_zpow, Prod.pow_snd, Prod.snd_mul, one_zpow, mul_one] at h2
    exact ⟨n, h2⟩
  obtain ⟨y, hyo, hyc, hyd⟩ := hB d hdo
  refine ⟨(1, y), ?_, fun f hf => ?_, fun hm => hyd ?_⟩
  · rw [Prod.orderOf]
    simp [hyo]
  · obtain ⟨n, hn⟩ := hsnd f hf
    have hc : f.2 * y = y * f.2 := by
      rw [← hn]
      exact (hyc.zpow_left n).eq
    ext <;> simp [hc]
  · simpa using hsnd _ hm

end Prod

section J2

theorem exists_commute_three_of_j2 (h415 : Sec4.Item4_15) {G : Type} [Group G] [Finite G]
    (hG : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.J2)) {d : G} (hd : orderOf d = 3) :
    ∃ y : G, orderOf y = 3 ∧ Commute d y ∧ y ∉ Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdp : IsPGroup 3 (Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd, pow_one])
  obtain ⟨P, hP⟩ := hdp.exists_le_sylow
  obtain ⟨hext, h27, hexp⟩ := (h415 G hG P _ rfl _ rfl).1.1
  have hdP : d ∈ (P : Subgroup G) := hP (Subgroup.mem_zpowers d)
  have hpow : ∀ x ∈ (P : Subgroup G), x ^ 3 = 1 := fun x hx => by
    have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : ↥(P : Subgroup G))
    rw [hexp] at h
    simpa using congrArg Subtype.val h
  have hord : ∀ x ∈ (P : Subgroup G), x ≠ 1 → orderOf x = 3 := fun x hx h1 =>
    orderOf_eq_prime (hpow x hx) h1
  have hcardZ : Nat.card (Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, hd]
  by_cases hdc : ∀ p ∈ (P : Subgroup G), Commute d p
  · have hnle : ¬ (P : Subgroup G) ≤ Subgroup.zpowers d := fun hle => by
      have h := Subgroup.card_le_of_le hle
      rw [h27, hcardZ] at h
      norm_num at h
    obtain ⟨y, hyP, hyd⟩ := SetLike.not_le_iff_exists.mp hnle
    have hy1 : y ≠ 1 := fun h => hyd (h ▸ one_mem _)
    exact ⟨y, hord y hyP hy1, hdc y hyP, hyd⟩
  · push Not at hdc
    obtain ⟨p, hpP, hpd⟩ := hdc
    have hZ : Nat.card (Subgroup.center ↥(P : Subgroup G)) = 3 := hext.2.2.2
    have hne : Subgroup.center ↥(P : Subgroup G) ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hZ
      norm_num at hZ
    obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
    have hzc : ∀ q ∈ (P : Subgroup G), q * (z : G) = (z : G) * q := fun q hq =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨q, hq⟩)
    have hzo : orderOf (z : G) = 3 := hord _ z.2 hz1'
    refine ⟨z, hzo, hzc d hdP, fun hzd => hpd ?_⟩
    have hle : Subgroup.zpowers (z : G) ≤ Subgroup.zpowers d := Subgroup.zpowers_le.mpr hzd
    have heq : Subgroup.zpowers (z : G) = Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardZ, Nat.card_zpowers, hzo])
    have hdz : d ∈ Subgroup.zpowers (z : G) := heq ▸ Subgroup.mem_zpowers d
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hdz
    rw [← hm]
    exact (show Commute (z : G) p from (hzc p hpP).symm).zpow_left m

theorem exists_not_commute_of_j2 (h415 : Sec4.Item4_15) {G : Type} [Group G] [Finite G]
    (hG : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.J2)) : ∃ x y : G, x * y ≠ y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 G))
  obtain ⟨hext, -, -⟩ := (h415 G hG P _ rfl _ rfl).1.1
  by_contra hc
  push Not at hc
  have hcomm : commutator ↥(P : Subgroup G) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact Subtype.ext (hc y x)
  have hZ := hext.2.2.2
  rw [← hext.2.1, hcomm, Subgroup.card_bot] at hZ
  norm_num at hZ

end J2

theorem conj_injective_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hnc : ∃ x y : G, x * y ≠ y * x) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases Subgroup.Normal.eq_bot_or_eq_top (MulAut.conj : G →* MulAut G).ker with h | h
  · exact h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    have hx : x ∈ (MulAut.conj : G →* MulAut G).ker := h ▸ Subgroup.mem_top x
    have h1 := congrArg (fun α : MulAut G => α y) (MonoidHom.mem_ker.mp hx)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    apply hxy
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [h1]

theorem conj_injective_of_mulEquiv {X G : Type*} [Group X] [Group G] (φ : X ≃* G)
    (h : Function.Injective (MulAut.conj : G →* MulAut G)) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro x y hxy
  apply φ.injective
  apply h
  ext g
  have := congrArg (fun α : MulAut X => φ (α (φ.symm g))) hxy
  simpa [MulAut.conj_apply] using this

theorem mem_range_conj_of_mulEquiv {X G : Type*} [Group X] [Group G] (φ : X ≃* G)
    (h : ∀ β : MulAut G, β ^ 3 = 1 → β ∈ (MulAut.conj : G →* MulAut G).range)
    (α : MulAut X) (hα : α ^ 3 = 1) : α ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨g, hg⟩ := h (MulAut.congr φ α) (by rw [← map_pow, hα, map_one])
  refine ⟨φ.symm g, ?_⟩
  ext x
  have := congrArg (fun β : MulAut G => φ.symm (β (φ x))) hg
  simpa [MulAut.congr_apply, MulAut.conj_apply] using this

theorem a5_facts :
    Function.Injective (MulAut.conj : alternatingGroup (Fin 5) →* MulAut _) ∧
      ∀ α : MulAut (alternatingGroup (Fin 5)), α ^ 3 = 1 →
        α ∈ (MulAut.conj : alternatingGroup (Fin 5) →* MulAut _).range := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by norm_num) (by norm_num)
  refine ⟨fun x y hxy => ?_, fun α hα => ?_⟩
  · have h : MulAut.conjNormal (H := alternatingGroup (Fin 5)) (x : Perm (Fin 5)) =
        MulAut.conjNormal (H := alternatingGroup (Fin 5)) (y : Perm (Fin 5)) := by
      rw [MulAut.conjNormal_val, MulAut.conjNormal_val, hxy]
    exact Subtype.ext (hbij.1 h)
  · obtain ⟨σ, hσ⟩ := hbij.2 α
    have hσ3 : σ ^ 3 = 1 := by
      apply hbij.1
      rw [map_pow, hσ, hα, map_one]
    have hσA : σ ∈ alternatingGroup (Fin 5) := by
      rw [Perm.mem_alternatingGroup]
      have h := congrArg Perm.sign hσ3
      rw [map_pow, map_one] at h
      rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
      · exact h1
      · rw [h1] at h
        exact absurd h (by decide)
    refine ⟨⟨σ, hσA⟩, ?_⟩
    rw [← hσ]
    exact (MulAut.conjNormal_val (H := alternatingGroup (Fin 5)) (h := ⟨σ, hσA⟩)).symm

end Wales1411W.HJProd

open Wales1411W Wales1411W.HJProd in
theorem ks1411HJCoreA5J2_of (hJs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2)
    (hJc : Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800) (h415 : Sec4.Item4_15)
    (hJaut : ∀ σ : MulAut CFSG.Blueprint.NativeSporadic.J2, σ ^ 3 = 1 →
      σ ∈ (MulAut.conj : CFSG.Blueprint.NativeSporadic.J2 →* _).range) :
    KS1411HJCoreA5J2 := by
  intro M _ _ Ybar Abar Xbar Rbar abar hset hX S T _ _ _ _
  exfalso
  obtain ⟨φ⟩ := hX
  haveI := HJInner.normal_X hset
  haveI : Finite (alternatingGroup (Fin 5) × CFSG.Blueprint.NativeSporadic.J2) :=
    Finite.of_equiv _ φ.toEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.J2 :=
    Finite.of_surjective
      (Prod.snd : alternatingGroup (Fin 5) × CFSG.Blueprint.NativeSporadic.J2 → _)
      Prod.snd_surjective
  have hA5 := a5_facts
  have hcA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    rfl
  have hAB : Nat.card (alternatingGroup (Fin 5)) < Nat.card CFSG.Blueprint.NativeSporadic.J2 := by
    rw [hcA5, hJc]
    norm_num
  have hJcen := conj_injective_of_simple (exists_not_commute_of_j2 h415 ⟨MulEquiv.refl _⟩)
  have hcen : Function.Injective (MulAut.conj : ↥Xbar →* MulAut ↥Xbar) :=
    conj_injective_of_mulEquiv φ (prod_conj_injective hA5.1 hJcen)
  have hinner : ∀ α : MulAut ↥Xbar, α ^ 3 = 1 →
      α ∈ (MulAut.conj : ↥Xbar →* MulAut ↥Xbar).range :=
    mem_range_conj_of_mulEquiv φ (mem_range_conj_of_pow_three hAB hA5.1 hA5.2 hJaut)
  have hAeq := HJInner.eq_inf_sup hset hcen hinner
  have h9 := HJInner.card_inf hset hcen hinner
  set E := ((Abar ⊓ Xbar).subgroupOf Xbar).map φ.toMonoidHom with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9]
  have hEmem : ∀ e ∈ E, ((φ.symm e : ↥Xbar) : M) ∈ Abar := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using (Subgroup.mem_subgroupOf.mp hx).1
  have hEcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := by
    intro e he f hf
    have h : ((φ.symm e : ↥Xbar) : M) * (φ.symm f : ↥Xbar) =
        (φ.symm f : ↥Xbar) * (φ.symm e : ↥Xbar) :=
      congrArg Subtype.val (hset.isElemAbelian.1.is_comm.comm ⟨_, hEmem e he⟩ ⟨_, hEmem f hf⟩)
    apply φ.symm.injective
    rw [map_mul, map_mul]
    exact Subtype.ext h
  have hE3 : ∀ e ∈ E, e ^ 3 = 1 := by
    intro e he
    apply φ.symm.injective
    apply Subtype.ext
    rw [map_pow, map_one]
    simpa using hset.isElemAbelian.2 _ (hEmem e he)
  have hc0mem : (swap (0 : Fin 5) 1 * swap 0 2) ∈ alternatingGroup (Fin 5) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    decide
  have hc0 : orderOf (⟨_, hc0mem⟩ : alternatingGroup (Fin 5)) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => ?_
    · show (swap (0 : Fin 5) 1 * swap 0 2) ^ 3 = 1
      decide
    · have h' : (swap (0 : Fin 5) 1 * swap 0 2) = 1 := congrArg Subtype.val h
      exact absurd h' (by decide)
  have hJd := @exists_commute_three_of_j2 h415 CFSG.Blueprint.NativeSporadic.J2 _ _
    ⟨MulEquiv.refl _⟩
  have hA9 : ¬ 9 ∣ Nat.card (alternatingGroup (Fin 5)) := by rw [hcA5]; norm_num
  obtain ⟨y, hyo, hyc, hyE⟩ :=
    exists_three_centralizer_not_mem hA9 hc0 (fun d hd => hJd hd) E hEcomm hE3 hE9
  set y0 : M := ((φ.symm y : ↥Xbar) : M) with hy0
  have hy0Y : y0 ∈ Ybar := hset.le_Y (φ.symm y).2
  have hy0o : orderOf y0 = 3 := by
    rw [hy0, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hyo]
  have hy0C : y0 ∈ Subgroup.centralizer (Abar : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    have hle : Abar ≤ Subgroup.centralizer ({y0} : Set M) := by
      rw [hAeq]
      refine sup_le (fun g hg => ?_) ?_
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hgE : φ ⟨g, hg.2⟩ ∈ E := ⟨⟨g, hg.2⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
        have h := congrArg (fun z => ((φ.symm z : ↥Xbar) : M)) (hyc _ hgE)
        simpa [hy0] using h
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hset.le_centralizer_a hy0Y)).symm
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  have hy0A := hset.mem_A_of_three y0 hy0Y hy0C hy0o
  apply hyE
  refine ⟨φ.symm y, Subgroup.mem_subgroupOf.mpr ⟨hy0A, (φ.symm y).2⟩, ?_⟩
  simp

theorem ks1411HJCoreA5J2 :
    KS1411HJCoreA5J2 :=
  ks1411HJCoreA5J2_of CFSG.Sporadic.J2.isSimpleGroup_J2 CFSG.Sporadic.J2.card_J2
    Sec4.Sporadic.rank3II_4_15
    (fun _ hσ => Sec17.j2_mem_range_conj_of_pow_eq_one (k := 1) ⟨MulEquiv.refl _⟩
      (by rw [pow_one]; exact hσ))

end CFSG.RankThree.PartTwo.Sec14
