module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.GroupTheory.ElemAbelianClosure
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggInduced_unique {L' R : Type*} [Group L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) {a : MulAut L'} {φ₁ φ₂ : MulAut R}
    (h₁ : ∀ l, φ₁ (ψ l) = ψ (a l)) (h₂ : ∀ l, φ₂ (ψ l) = ψ (a l)) : φ₁ = φ₂ := by
  ext r
  obtain ⟨l, rfl⟩ := hψ r
  rw [h₁, h₂]

theorem ggInducedHom_exists {L' R : Type*} [Group L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (A : Subgroup (MulAut L'))
    (hA : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l)) :
    ∃ Ind : A →* MulAut R, ∀ (a : A) (l : L'), Ind a (ψ l) = ψ ((a : MulAut L') l) := by
  choose φ hφ using fun a : A => hA a a.2
  refine ⟨{ toFun := φ, map_one' := ?_, map_mul' := ?_ }, fun a l => hφ a l⟩
  · apply ggInduced_unique hψ (a := ((1 : A) : MulAut L'))
    · intro l; exact hφ 1 l
    · intro l
      rw [MulAut.one_apply, Subgroup.coe_one, MulAut.one_apply]
  · intro a b
    apply ggInduced_unique hψ (a := ((a * b : A) : MulAut L'))
    · intro l; exact hφ (a * b) l
    · intro l
      rw [MulAut.mul_apply, hφ b, hφ a, Subgroup.coe_mul, MulAut.mul_apply]

theorem ggIsElemAbelian_range {p : ℕ} {G M : Type*} [Group G] [Group M] {A₀ A : Subgroup G}
    (hA₀ : A₀ ≤ A) (hA : IsElemAbelian p A) (f : A₀ →* M) : IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul]
    obtain ⟨a₀, ha₀⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨b₀, hb₀⟩ := MonoidHom.mem_range.mp b.2
    rw [← ha₀, ← hb₀, ← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (hA.comm (hA₀ a₀.2) (hA₀ b₀.2)))
  · obtain ⟨a₀, ha₀⟩ := MonoidHom.mem_range.mp hx
    have ha₀p : a₀ ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, hA.2 _ (hA₀ a₀.2)]
    rw [← ha₀, ← map_pow, ha₀p, map_one]

theorem ggCyclicSplit {p : ℕ} (hp : p.Prime) {G M : Type*} [Group G] [Group M]
    {U U₁ : Subgroup G} (hU₁ : U₁ ≤ U) (hexp : ∀ u ∈ U, u ^ p = 1) (ρ : U →* M)
    {J S : Subgroup M} (hN : (J.subgroupOf S).Normal)
    (hcyc : ∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) (hρS : ∀ u, ρ u ∈ S)
    (hmem : ∀ u : U, (u : G) ∈ U₁ ↔ ρ u ∈ J) :
    Nat.card U ≤ p * Nat.card U₁ ∧
      ∀ b ∈ U, b ∉ U₁ → ∀ u ∈ U, ∃ k : ℤ, u * b ^ k ∈ U₁ := by
  have := hN
  have hQ : IsCyclic (S ⧸ J.subgroupOf S) := by
    obtain ⟨g₀, hg₀, hgen⟩ := hcyc
    refine ⟨⟨(QuotientGroup.mk (⟨g₀, hg₀⟩ : S) : S ⧸ J.subgroupOf S), fun x => ?_⟩⟩
    induction x using QuotientGroup.induction_on with
    | H s =>
      obtain ⟨k, hk⟩ := hgen s s.2
      have h1 : (QuotientGroup.mk ((⟨g₀, hg₀⟩ : S) ^ k * s) : S ⧸ J.subgroupOf S) = 1 := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa using hk
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
      refine ⟨-k, ?_⟩
      change (QuotientGroup.mk (⟨g₀, hg₀⟩ : S) : S ⧸ J.subgroupOf S) ^ (-k) = _
      rw [zpow_neg]
      exact inv_eq_of_mul_eq_one_right h1
  let ρ' : U →* S := ρ.codRestrict S hρS
  let φ : U →* S ⧸ J.subgroupOf S := (QuotientGroup.mk' (J.subgroupOf S)).comp ρ'
  have hφapp : ∀ u : U, φ u = (ρ' u : S ⧸ J.subgroupOf S) := fun _ => rfl
  have hker_mem : ∀ u : U, u ∈ φ.ker ↔ (u : G) ∈ U₁ := by
    intro u
    have hiff : φ u = 1 ↔ ρ u ∈ J := by
      rw [hφapp u, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact Iff.rfl
    rw [MonoidHom.mem_ker, hiff, hmem u]
  let e : φ.ker ≃ U₁ :=
    { toFun := fun u => ⟨(u : U), (hker_mem u).mp u.2⟩
      invFun := fun x => ⟨⟨(x : G), hU₁ x.2⟩, (hker_mem ⟨(x : G), hU₁ x.2⟩).mpr x.2⟩
      left_inv := fun u => by ext <;> rfl
      right_inv := fun x => by ext <;> rfl }
  have hcardK : Nat.card φ.ker = Nat.card U₁ := Nat.card_congr e
  haveI : IsCyclic φ.range := Subgroup.isCyclic φ.range
  have hpow : ∀ y ∈ φ.range, y ^ p = 1 := by
    intro y hy
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hy
    have hu_pow : u ^ p = 1 := by
      apply Subtype.ext
      simpa using hexp (u : G) u.2
    rw [← map_pow, hu_pow, map_one]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := φ.range)
  have horder : orderOf g = Nat.card φ.range := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := by
    apply Subtype.ext
    simpa using hpow (g : S ⧸ J.subgroupOf S) g.2
  have hdvd : Nat.card φ.range ∣ p := by
    rw [← horder]
    exact orderOf_dvd_of_pow_eq_one hgp
  have hcard_le : Nat.card φ.range ≤ p := by
    rcases hp.eq_one_or_self_of_dvd (Nat.card φ.range) hdvd with h | h
    · rw [h]; exact hp.one_lt.le
    · rw [h]
  have hcard_ne : Nat.card φ.range ≠ 0 := by
    rcases hp.eq_one_or_self_of_dvd (Nat.card φ.range) hdvd with h | h
    · rw [h]; exact one_ne_zero
    · rw [h]; exact hp.ne_zero
  haveI : Finite φ.range := Nat.finite_of_card_ne_zero hcard_ne
  have hcardU : Nat.card U = Nat.card U₁ * Nat.card φ.range := by
    rw [← Subgroup.card_mul_index (H := φ.ker), Subgroup.index_ker φ, hcardK]
  have hmain : Nat.card U ≤ p * Nat.card U₁ := by
    rw [hcardU]
    calc Nat.card U₁ * Nat.card φ.range ≤ Nat.card U₁ * p := Nat.mul_le_mul_left _ hcard_le
      _ = p * Nat.card U₁ := mul_comm _ _
  refine ⟨hmain, fun b hb hbU₁ u hu => ?_⟩
  let q : φ.range := ⟨φ ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩⟩
  have hq_ne : q ≠ 1 := by
    intro h
    have hker : φ ⟨b, hb⟩ = 1 := congrArg Subtype.val h
    exact hbU₁ ((hker_mem ⟨b, hb⟩).mp hker)
  have hq_pow : q ^ p = 1 := by
    apply Subtype.ext
    simpa using hpow (q : S ⧸ J.subgroupOf S) q.2
  have hdvd_q : orderOf q ∣ p := orderOf_dvd_of_pow_eq_one hq_pow
  have horder_q : orderOf q = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf q) hdvd_q with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hq_ne
    · exact h
  have hcard_zp : Nat.card (Subgroup.zpowers q) = p := by
    rw [Nat.card_zpowers, horder_q]
  have hzp_eq : Subgroup.zpowers q = ⊤ := by
    refine Subgroup.eq_of_le_of_card_ge le_top ?_
    rw [Subgroup.card_top, hcard_zp]
    exact hcard_le
  have hu_zp : (⟨φ ⟨u, hu⟩, ⟨⟨u, hu⟩, rfl⟩⟩ : φ.range) ∈ Subgroup.zpowers q := by
    rw [hzp_eq]
    exact Subgroup.mem_top _
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hu_zp
  have hm' : (φ ⟨b, hb⟩ : S ⧸ J.subgroupOf S) ^ m = φ ⟨u, hu⟩ := by
    simpa using congrArg Subtype.val hm
  refine ⟨-m, ?_⟩
  have hker_mem' : (⟨u, hu⟩ * ⟨b, hb⟩ ^ (-m) : U) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_zpow, ← hm']
    group
  have hmemU₁ : ((⟨u, hu⟩ * ⟨b, hb⟩ ^ (-m) : U) : G) ∈ U₁ := (hker_mem _).mp hker_mem'
  simpa using hmemU₁

section Transfer

variable {L' : Type} [Group L'] {A A₀ : Subgroup (MulAut L')} {H : Subgroup L'}

theorem ggTransfer_decomp {b : MulAut L'} (hbH : ∀ l ∈ H, b l = l)
    (hgen : ∀ u ∈ A, ∃ k : ℤ, u * b ^ k ∈ A₀) :
    ∀ u ∈ A, ∃ a₀ ∈ A₀, ∀ l ∈ H, u l = a₀ l := by
  intro u hu
  obtain ⟨k, hk⟩ := hgen u hu
  refine ⟨u * b ^ k, hk, fun l hl => ?_⟩
  have hbfix : b ∈ fixingSubgroup (MulAut L') (H : Set L') := by
    rw [mem_fixingSubgroup_iff]
    exact fun y hy => hbH y hy
  have hbpow : b ^ k ∈ fixingSubgroup (MulAut L') (H : Set L') := zpow_mem hbfix k
  have hfixl : (b ^ k) l = l := by
    simpa using (mem_fixingSubgroup_iff (M := MulAut L') (s := (H : Set L'))).mp hbpow l hl
  rw [MulAut.mul_apply, hfixl]

theorem ggRestrict_conj (res : A₀ →* MulAut H)
    (hres : ∀ (a : A₀) (l : H), ((res a l : H) : L') = (a : MulAut L') l) (n : H) (a c : A₀)
    (hc : (c : MulAut L') = MulAut.conj (n : L') * (a : MulAut L') * (MulAut.conj (n : L'))⁻¹) :
    res c = MulAut.conj n * res a * (MulAut.conj n)⁻¹ := by
  ext l
  rw [hres c l, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hres a ((MulAut.conj n)⁻¹ l), MulAut.conj_inv_apply]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hc, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]

theorem ggTransfer_first {p : ℕ} (res : A₀ →* MulAut H)
    (hres : ∀ (a : A₀) (l : H), ((res a l : H) : L') = (a : MulAut L') l)
    (hdec : ∀ u ∈ A, ∃ a₀ ∈ A₀, ∀ l ∈ H, u l = a₀ l) {W₀ : Set H}
    (h1 : ∀ n ∈ W₀, ∀ a ∈ res.range, (n * (a n)⁻¹) ^ p = 1 ∧
      ∀ a' ∈ res.range, a' (n * (a n)⁻¹) = n * (a n)⁻¹) :
    ∀ n ∈ (Subtype.val '' W₀ : Set L'), ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧
      ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹ := by
  rintro n ⟨n₀, hn₀, rfl⟩ a ha
  obtain ⟨a₀, ha₀, ha₀eq⟩ := hdec a ha
  let a₀' : A₀ := ⟨a₀, ha₀⟩
  have han : a (n₀ : L') = (a₀' : MulAut L') (n₀ : L') := ha₀eq n₀ n₀.property
  have hresn : ((res a₀' n₀ : H) : L') = (a₀' : MulAut L') (n₀ : L') := hres a₀' n₀
  set m : H := n₀ * (res a₀' n₀)⁻¹ with hm
  have hval : (n₀ : L') * (a (n₀ : L'))⁻¹ = (m : L') := by
    rw [han, ← hresn]
    simp [hm]
  rw [hval]
  constructor
  · have h1a : m ^ p = 1 := by
      have h := (h1 n₀ hn₀ (res a₀') ⟨a₀', rfl⟩).1
      rwa [← hm] at h
    rw [← Subgroup.coe_pow, h1a, Subgroup.coe_one]
  · intro a' ha'
    obtain ⟨a₀'', ha₀'', ha₀''eq⟩ := hdec a' ha'
    let b₀ : A₀ := ⟨a₀'', ha₀''⟩
    have ha'm : a' (m : L') = (b₀ : MulAut L') (m : L') := ha₀''eq m m.property
    have hresm : ((res b₀ m : H) : L') = (b₀ : MulAut L') (m : L') := hres b₀ m
    have h1b : res b₀ m = m := by
      have h := (h1 n₀ hn₀ (res a₀') ⟨a₀', rfl⟩).2 (res b₀) ⟨b₀, rfl⟩
      rwa [← hm] at h
    calc a' (m : L') = (b₀ : MulAut L') (m : L') := ha'm
      _ = ((res b₀ m : H) : L') := hresm.symm
      _ = (m : L') := by rw [h1b]

theorem ggTransfer_selfCent {p : ℕ} (res : A₀ →* MulAut H)
    (hres : ∀ (a : A₀) (l : H), ((res a l : H) : L') = (a : MulAut L') l)
    (hdec : ∀ u ∈ A, ∃ a₀ ∈ A₀, ∀ l ∈ H, u l = a₀ l) (hsc : GGTorusSelfCent p A)
    (hconj : ∀ n ∈ H, MulAut.conj n ∈ A → MulAut.conj n ∈ A₀) :
    GGTorusSelfCent p res.range := by
  intro n hn hnp
  have hfixA : ∀ a ∈ A, a (n : L') = (n : L') := by
    intro a ha
    obtain ⟨a₀, ha₀, haeq⟩ := hdec a ha
    rw [haeq (n : L') n.2]
    exact (hres ⟨a₀, ha₀⟩ n).symm.trans
      (congrArg Subtype.val (hn (res ⟨a₀, ha₀⟩) ⟨⟨a₀, ha₀⟩, rfl⟩))
  have hnp' : (n : L') ^ p = 1 := by
    rw [← Subgroup.coe_pow, hnp, Subgroup.coe_one]
  have hconjA : MulAut.conj (n : L') ∈ A := hsc (n : L') hfixA hnp'
  have hconjA₀ : MulAut.conj (n : L') ∈ A₀ := hconj (n : L') n.2 hconjA
  refine ⟨⟨MulAut.conj (n : L'), hconjA₀⟩, ?_⟩
  ext l
  rw [hres]
  simp [MulAut.conj_apply]

theorem ggTransfer_second (res : A₀ →* MulAut H)
    (hres : ∀ (a : A₀) (l : H), ((res a l : H) : L') = (a : MulAut L') l)
    (hinj : Function.Injective res) (hA₀ : A₀ ≤ A)
    (hnorm : ∀ n ∈ H, ∀ a ∈ A₀, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A →
      MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A₀) {W₀ : Set H}
    (h2 : (∀ n ∈ W₀, ∀ a ∈ res.range, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ res.range) →
      ∀ a₀ ∈ res.range, a₀ ≠ 1 →
        ∃ n ∈ W₀, MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀) :
    (∀ n ∈ (Subtype.val '' W₀ : Set L'), ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A) →
      ∀ a₀ ∈ A₀, a₀ ≠ 1 → ∃ n ∈ (Subtype.val '' W₀ : Set L'),
        MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀ := by
  intro hN a₀ ha₀ ha₀ne
  have h2hyp : ∀ n ∈ W₀, ∀ a ∈ res.range,
      MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ res.range := by
    intro n hnW a ha
    obtain ⟨a', rfl⟩ := ha
    have hAN : MulAut.conj (n : L') * (a' : MulAut L')
        * (MulAut.conj (n : L'))⁻¹ ∈ A :=
      hN (n : L') ⟨n, hnW, rfl⟩ (a' : MulAut L') (hA₀ a'.2)
    have hA₀N : MulAut.conj (n : L') * (a' : MulAut L')
        * (MulAut.conj (n : L'))⁻¹ ∈ A₀ :=
      hnorm (n : L') n.2 a' a'.2 hAN
    let c : A₀ :=
      ⟨MulAut.conj (n : L') * (a' : MulAut L') * (MulAut.conj (n : L'))⁻¹, hA₀N⟩
    exact ⟨c, ggRestrict_conj res hres n a' c rfl⟩
  have hne : res ⟨a₀, ha₀⟩ ≠ 1 := by
    intro h
    apply ha₀ne
    have h1 : (⟨a₀, ha₀⟩ : A₀) = 1 := hinj (h.trans (map_one res).symm)
    simpa using congrArg Subtype.val h1
  obtain ⟨n₀, hn₀W, hn₀bad⟩ := h2 h2hyp (res ⟨a₀, ha₀⟩) ⟨⟨a₀, ha₀⟩, rfl⟩ hne
  refine ⟨(n₀ : L'), ⟨n₀, hn₀W, rfl⟩, ?_⟩
  intro h
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
  let c : A₀ := (⟨a₀, ha₀⟩ : A₀) ^ m
  have hc : (c : MulAut L') =
      MulAut.conj (n₀ : L') * a₀ * (MulAut.conj (n₀ : L'))⁻¹ := by
    change (↑(((⟨a₀, ha₀⟩ : A₀) ^ m)) : MulAut L') =
      MulAut.conj (n₀ : L') * a₀ * (MulAut.conj (n₀ : L'))⁻¹
    rw [Subgroup.coe_zpow]
    exact hm
  have hr := ggRestrict_conj res hres n₀ ⟨a₀, ha₀⟩ c hc
  apply hn₀bad
  rw [← hr]
  exact Subgroup.mem_zpowers_iff.mpr ⟨m, (map_zpow res ⟨a₀, ha₀⟩ m).symm⟩

end Transfer

end CFSG.StandardType

end
