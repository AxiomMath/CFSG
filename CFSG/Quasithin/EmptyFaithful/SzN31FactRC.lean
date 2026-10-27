module

public import CFSG.Quasithin.EmptyFaithful.SzN31FactRE
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Data.Set.Finite.Lemmas

public section

namespace CFSG.Quasithin.SzN31

section FactRC

variable {Q : Type*} [Group Q]

theorem exists_quotient_action (N : Subgroup Q) [N.Normal] {I : Type*} (σ : I → MulAut Q)
    (hσ : ∀ b x, σ b (σ b x) = x) (hσc : ∀ b c x, σ b (σ c x) = σ c (σ b x))
    (hNi : ∀ b, ∀ x ∈ N, σ b x ∈ N) :
    ∃ τ : I → MulAut (Q ⧸ N), (∀ b (x : Q), τ b (x : Q ⧸ N) = ((σ b x : Q) : Q ⧸ N)) ∧
      (∀ b z, τ b (τ b z) = z) ∧ (∀ b c z, τ b (τ c z) = τ c (τ b z)) := by
  have hmap : ∀ b, Subgroup.map ((σ b : MulAut Q) : Q →* Q) N = N := by
    intro b
    ext y
    refine ⟨?_, fun hy => ⟨σ b y, hNi b y hy, hσ b y⟩⟩
    rintro ⟨x, hx, rfl⟩
    exact hNi b x hx
  have hmk : ∀ b (x : Q), QuotientGroup.congr N N (σ b) (hmap b) (x : Q ⧸ N) = ((σ b x : Q) : Q ⧸ N) :=
    fun b x => QuotientGroup.congr_mk _ _ _ _ _
  refine ⟨fun b => QuotientGroup.congr N N (σ b) (hmap b), hmk, ?_, ?_⟩
  · intro b z
    induction z using QuotientGroup.induction_on with
    | H x => rw [hmk, hmk, hσ]
  · intro b c z
    induction z using QuotientGroup.induction_on with
    | H x => rw [hmk, hmk, hmk, hmk, hσc]

theorem exists_central_invariant_line {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) {I : Type*} (τ : I → MulAut G) (hτ : ∀ b x, τ b (τ b x) = x)
    (hτc : ∀ b c x, τ b (τ c x) = τ c (τ b x)) {Cb : Subgroup G} [Cb.Normal] (hCb : Cb ≠ ⊥)
    (hCbi : ∀ b, ∀ x ∈ Cb, τ b x ∈ Cb) :
    ∃ L : Subgroup G, L ≤ Cb ∧ L ≤ Subgroup.center G ∧ Nat.card L = p ∧ ∀ b, ∀ x ∈ L, τ b x ∈ L := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsNilpotent G := hG.isNilpotent
  have hZ : Cb ⊓ Subgroup.center G ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hCb
  have hZc : ∀ x ∈ Cb ⊓ Subgroup.center G, ∀ y ∈ Cb ⊓ Subgroup.center G, x * y = y * x :=
    fun x _ y hy => Subgroup.mem_center_iff.1 hy.2 x
  have hZi : ∀ b, ∀ x ∈ Cb ⊓ Subgroup.center G, τ b x ∈ Cb ⊓ Subgroup.center G := by
    intro b x hx
    refine ⟨hCbi b x hx.1, Subgroup.mem_center_iff.2 fun g => ?_⟩
    have h := Subgroup.mem_center_iff.1 hx.2 (τ b g)
    calc g * τ b x = τ b (τ b g * x) := by rw [map_mul, hτ]
      _ = τ b (x * τ b g) := by rw [h]
      _ = τ b x * g := by rw [map_mul, hτ]
  have hW : omegaOne p (Cb ⊓ Subgroup.center G) hZc ≠ ⊥ := by
    have hdvd : p ∣ Nat.card ↥(Cb ⊓ Subgroup.center G) :=
      ((hG.to_subgroup _).card_eq_or_dvd).resolve_left fun h => hZ (Subgroup.eq_bot_of_card_eq _ h)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    intro h
    have hxW : (x : G) ∈ omegaOne p (Cb ⊓ Subgroup.center G) hZc :=
      ⟨x.2, by rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]⟩
    rw [h, Subgroup.mem_bot] at hxW
    have h1 : x = 1 := Subtype.ext hxW
    rw [h1, orderOf_one] at hx
    exact hp.one_lt.ne hx
  obtain ⟨L, hLW, hLp, hLi⟩ := exists_invariant_line_family hp hp2 τ hτ hτc hW
    (fun x hx y hy => hZc x hx.1 y hy.1) (fun x hx => hx.2)
    (fun b x hx => ⟨hZi b x hx.1, by rw [← map_pow, hx.2, map_one]⟩)
  exact ⟨L, fun x hx => (hLW hx).1.1, fun x hx => (hLW hx).1.2, hLp, hLi⟩

theorem exists_invariant_extension {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [Finite Q] (hQ : IsPGroup p Q)
    {I : Type*} (σ : I → MulAut Q) (hσ : ∀ b x, σ b (σ b x) = x)
    (hσc : ∀ b c x, σ b (σ c x) = σ c (σ b x)) {N : Subgroup Q} (hNn : N.Normal)
    (hNi : ∀ b, ∀ x ∈ N, σ b x ∈ N) (hNc : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) {y : Q}
    (hy : ∀ n ∈ N, y * n = n * y) (hyN : y ∉ N) :
    ∃ M : Subgroup Q, M.Normal ∧ (∀ b, ∀ x ∈ M, σ b x ∈ M) ∧ (∀ x ∈ M, ∀ z ∈ M, x * z = z * x) ∧
      N ≤ M ∧ ∃ x ∈ M, x ∉ N := by
  have := hNn
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨C, hCmem, hCn⟩ : ∃ C : Subgroup Q, (∀ c, c ∈ C ↔ ∀ n ∈ N, n * c = c * n) ∧ C.Normal :=
    ⟨Subgroup.centralizer (N : Set Q), fun c => Subgroup.mem_centralizer_iff, Subgroup.normal_centralizer⟩
  have := hCn
  have hNC : ∀ n ∈ N, n ∈ C := fun n hn => (hCmem n).2 fun m hm => hNc m hm n hn
  have hCi : ∀ b, ∀ c ∈ C, σ b c ∈ C := by
    intro b c hc
    refine (hCmem _).2 fun n hn => ?_
    have h := (hCmem c).1 hc (σ b n) (hNi b n hn)
    calc n * σ b c = σ b (σ b n * c) := by rw [map_mul, hσ]
      _ = σ b (c * σ b n) := by rw [h]
      _ = σ b c * n := by rw [map_mul, hσ]
  obtain ⟨τ, hτmk, hτ, hτc⟩ := exists_quotient_action N σ hσ hσc hNi
  have : (C.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map hCn _ (QuotientGroup.mk'_surjective N)
  have hCb0 : C.map (QuotientGroup.mk' N) ≠ ⊥ := by
    intro h
    have hyC : y ∈ C := (hCmem y).2 fun n hn => (hy n hn).symm
    have h1 : QuotientGroup.mk' N y ∈ C.map (QuotientGroup.mk' N) := Subgroup.mem_map_of_mem _ hyC
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply] at h1
    exact hyN ((QuotientGroup.eq_one_iff y).1 h1)
  have hCbi : ∀ b, ∀ x ∈ C.map (QuotientGroup.mk' N), τ b x ∈ C.map (QuotientGroup.mk' N) := by
    intro b x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨σ b c, hCi b c hc, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hτmk]
  obtain ⟨L, hLC, hLZ, hLp, hLi⟩ :=
    exists_central_invariant_line hp hp2 (hQ.to_quotient N) τ hτ hτc hCb0 hCbi
  obtain ⟨M, hMmem⟩ : ∃ M : Subgroup Q, ∀ m : Q, m ∈ M ↔ ((m : Q) : Q ⧸ N) ∈ L :=
    ⟨L.comap (QuotientGroup.mk' N), fun m => Iff.rfl⟩
  have hMn : M.Normal := ⟨fun m hm g => by
    rw [hMmem] at hm ⊢
    have h1 : (g : Q ⧸ N) * (m : Q ⧸ N) = (m : Q ⧸ N) * (g : Q ⧸ N) :=
      Subgroup.mem_center_iff.1 (hLZ hm) g
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, mul_assoc, mul_inv_cancel,
      mul_one]
    exact hm⟩
  have hMi : ∀ b, ∀ x ∈ M, σ b x ∈ M := by
    intro b x hx
    rw [hMmem] at hx ⊢
    rw [← hτmk]
    exact hLi b _ hx
  have hMC : ∀ m ∈ M, m ∈ C := by
    intro m hm
    obtain ⟨c, hc, hcm⟩ := Subgroup.mem_map.1 (hLC ((hMmem m).1 hm))
    have hn : c⁻¹ * m ∈ N := QuotientGroup.eq.1 (by rwa [QuotientGroup.mk'_apply] at hcm)
    simpa using C.mul_mem hc (hNC _ hn)
  have hNM : N ≤ M := fun n hn => (hMmem n).2 (by rw [(QuotientGroup.eq_one_iff n).2 hn]; exact L.one_mem)
  have hL1 : ∃ a : L, a ≠ 1 := by
    refine Subgroup.ne_bot_iff_exists_ne_one.1 fun h => ?_
    rw [h, Subgroup.card_bot] at hLp
    exact hp.one_lt.ne hLp
  obtain ⟨a, ha⟩ := hL1
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (a : Q ⧸ N)
  have hxM : x ∈ M := (hMmem x).2 (hx ▸ a.2)
  have hxN : x ∉ N := fun h => ha (Subtype.ext (hx.symm.trans ((QuotientGroup.eq_one_iff x).2 h)))
  have hgen : Subgroup.zpowers a = ⊤ := zpowers_eq_top_of_prime_card hLp ha
  have hform : ∀ m ∈ M, ∃ k : ℤ, ∃ n ∈ N, m = x ^ k * n := by
    intro m hm
    have hmem : (⟨(m : Q ⧸ N), (hMmem m).1 hm⟩ : L) ∈ Subgroup.zpowers a := by
      rw [hgen]
      exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine ⟨k, (x ^ k)⁻¹ * m, ?_, by group⟩
    apply QuotientGroup.eq.1
    rw [QuotientGroup.mk_zpow, hx]
    exact congrArg Subtype.val hk
  have hxc : ∀ n ∈ N, Commute n x := fun n hn => (hCmem x).1 (hMC x hxM) n hn
  have hMc : ∀ u ∈ M, ∀ v ∈ M, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, n, hn, rfl⟩ := hform u hu
    obtain ⟨j, n', hn', rfl⟩ := hform v hv
    exact (Commute.mul_left
      (Commute.mul_right (Commute.zpow_zpow_self x i j) ((hxc n' hn').symm.zpow_left i))
      (Commute.mul_right ((hxc n hn).zpow_right j) (hNc n hn n' hn' : Commute n n'))).eq
  exact ⟨M, hMn, hMi, hMc, hNM, x, hxM, hxN⟩

end FactRC

theorem exists_selfCentralizing_normal_abelian_invariant {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Type} [Group Q]
    [Finite Q] (hQ : IsPGroup p Q) {Bh : Type} [Group Bh] (act : Bh →* MulAut Q) (hB : ∀ b : Bh, b * b = 1) :
    ∃ N : Subgroup Q, N.Normal ∧ (∀ b : Bh, ∀ x ∈ N, act b x ∈ N) ∧
      (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) ∧ (∀ y : Q, (∀ n ∈ N, y * n = n * y) → y ∈ N) := by
  let S : Set (Subgroup Q) := {N | N.Normal ∧ (∀ b : Bh, ∀ x ∈ N, act b x ∈ N) ∧
    (∀ x ∈ N, ∀ y ∈ N, x * y = y * x)}
  have hSne : S.Nonempty :=
    ⟨⊥, Subgroup.normal_bot, fun b x hx => by rw [Subgroup.mem_bot.1 hx, map_one]; exact Subgroup.one_mem _,
      fun x hx y hy => by rw [Subgroup.mem_bot.1 hx, Subgroup.mem_bot.1 hy]⟩
  obtain ⟨N, ⟨hNn, hNi, hNc⟩, hNmax⟩ :=
    Set.exists_max_image S (fun N : Subgroup Q => Nat.card N) (Set.toFinite S) hSne
  refine ⟨N, hNn, hNi, hNc, fun y hy => ?_⟩
  by_contra hyN
  obtain ⟨M, hMn, hMi, hMc, hNM, x, hxM, hxN⟩ :=
    exists_invariant_extension hp hp2 hQ (fun b => act b) (act_invol act hB) (act_comm act hB) hNn hNi hNc hy hyN
  have hMN : N = M := Subgroup.eq_of_le_of_card_ge hNM (hNmax M ⟨hMn, hMi, hMc⟩)
  exact hxN (hMN ▸ hxM)

end CFSG.Quasithin.SzN31
