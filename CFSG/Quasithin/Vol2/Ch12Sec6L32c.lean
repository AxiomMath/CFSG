module

public import CFSG.Quasithin.Vol2.Ch12Sec6L33f

public section

namespace CFSG.Quasithin.H13.L1232

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 S126P S126E
  S126L24 F126 L1233 Equiv

theorem card_inf_eq_64 {Q : Type*} [Group Q] [Finite Q] {P N : Subgroup Q} [N.Normal]
    (hP : Nat.card P = 2 ^ (Nat.card Q).factorization 2) (hN : Nat.card N = 60480)
    (hQ : Nat.card Q = 241920) : Nat.card ↥(P ⊓ N) = 64 := by
  have hPp : IsPGroup 2 ↥P := IsPGroup.of_card hP
  obtain ⟨k, hk⟩ := (hPp.to_le (inf_le_left : P ⊓ N ≤ P)).exists_card_eq
  have hk6 : k ≤ 6 := by
    by_contra h7
    have h1 : 2 ^ 7 ∣ Nat.card ↥(P ⊓ N) := by
      rw [hk]
      exact pow_dvd_pow 2 (by omega)
    have h2 := h1.trans (Subgroup.card_dvd_of_le (inf_le_right : P ⊓ N ≤ N))
    rw [hN] at h2
    norm_num at h2
  have hmul : Nat.card ↥(P ⊓ N) * N.relIndex P = Nat.card P := by
    have h := Subgroup.relIndex_mul_relIndex ⊥ (P ⊓ N) P bot_le inf_le_left
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left,
      Subgroup.inf_relIndex_left] at h
    exact h
  have hdvd : N.relIndex P ∣ N.index := Subgroup.relIndex_dvd_index_of_normal N P
  have hidx := N.card_mul_index
  rw [hN, hQ] at hidx
  have hi : N.index = 4 := by omega
  rw [hi] at hdvd
  have hr := Nat.le_of_dvd (by norm_num) hdvd
  have hf : (Nat.card Q).factorization 2 = 8 :=
    factorization_two_eq (by omega) (by rw [hQ]; norm_num) (by rw [hQ]; norm_num)
  rw [hf] at hP
  rw [hk, hP] at hmul
  rw [hk]
  interval_cases k <;> omega

theorem eq_bot_of_perfect {Q : Type*} [Group Q] [Group.IsSolvable Q] {X : Subgroup Q}
    (h : ⁅X, X⁆ = X) : X = ⊥ := by
  have key : ∀ n, X ≤ derivedSeries Q n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ, ← h]
      exact Subgroup.commutator_mono ih ih
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := Q)
  exact le_bot_iff.1 (hn ▸ key n)

theorem oTwoRes_top_eq {Q : Type} [Group Q] [Finite Q] {N : Subgroup Q} (hperf : ⁅N, N⁆ = N)
    (hsq : ∀ x : Q, x ^ 2 ∈ N) : oTwoRes (⊤ : Subgroup Q) = N := by
  apply le_antisymm
  · refine (Subgroup.closure_le N).2 ?_
    rintro x ⟨-, m, ⟨j, rfl⟩, hm⟩
    have e : x = (x ^ 2) ^ (j + 1) := by
      rw [← pow_mul, show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, hm, one_mul]
    rw [e]
    exact N.pow_mem (hsq x) _
  · set O := oTwoRes (⊤ : Subgroup Q) with hO
    have hOn : O.Normal := by
      have := le_normalizer_oTwoRes (⊤ : Subgroup Q)
      exact Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 this)
    have hp : IsPGroup 2 (Q ⧸ O) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (⊤ : Subgroup Q) (Subgroup.mem_top x)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hO, oTwoRes_eq_oTwoUpper]
      exact hk
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := hp.isNilpotent
    have hbot : N.map (QuotientGroup.mk' O) = ⊥ := by
      apply eq_bot_of_perfect
      rw [← Subgroup.map_commutator, hperf]
    intro x hx
    have : QuotientGroup.mk' O x ∈ N.map (QuotientGroup.mk' O) := Subgroup.mem_map_of_mem _ hx
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this

theorem mem_of_mem_sup {Q : Type} [Group Q] {P B : Subgroup Q} (hP : IsPGroup 2 ↥P)
    (hPB : P ≤ Subgroup.normalizer (B : Set Q)) {x : Q} (hx : x ∈ P ⊔ B) (h5 : x ^ 5 = 1) :
    x ∈ B := by
  rw [sup_comm] at hx
  obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup hPB hP hx
  have e : x = (x ^ 2 ^ k) ^ 2 ^ (3 * k) := by
    rw [← pow_mul, ← pow_add, show k + 3 * k = 4 * k by ring, pow_mul,
      pow_eq_pow_mod _ h5, Nat.pow_mod]
    norm_num
  rw [e]
  exact B.pow_mem hk _

variable {G : Type} [Group G]

theorem conj_eq_of_pow_five {V₁ : Subgroup G} (hV₁ : ∀ z ∈ V₁, z * z = 1) {y u : G}
    (hyV : ∀ z ∈ V₁, y * z = z * y) (hy5 : y ^ 5 = 1) (hu : (y * u * y⁻¹)⁻¹ * u ∈ V₁) :
    y * u * y⁻¹ = u := by
  set z := (y * u * y⁻¹)⁻¹ * u with hz
  have hyu : y * u * y⁻¹ = u * z⁻¹ := by rw [hz]; group
  have hzc : ∀ n : ℕ, y * (z ^ n)⁻¹ * y⁻¹ = (z ^ n)⁻¹ := fun n => by
    have h1 : y * z ^ n * y⁻¹ = z ^ n := by
      rw [(Commute.pow_right (hyV z hu) n).eq, mul_inv_cancel_right]
    calc y * (z ^ n)⁻¹ * y⁻¹ = (y * z ^ n * y⁻¹)⁻¹ := by group
      _ = (z ^ n)⁻¹ := by rw [h1]
  have key : ∀ n : ℕ, y ^ n * u * (y ^ n)⁻¹ = u * (z ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc y ^ (n + 1) * u * (y ^ (n + 1))⁻¹ = y * (y ^ n * u * (y ^ n)⁻¹) * y⁻¹ := by group
        _ = y * (u * (z ^ n)⁻¹) * y⁻¹ := by rw [ih]
        _ = (y * u * y⁻¹) * (y * (z ^ n)⁻¹ * y⁻¹) := by group
        _ = u * z⁻¹ * (z ^ n)⁻¹ := by rw [hyu, hzc]
        _ = u * (z ^ (n + 1))⁻¹ := by rw [pow_succ]; group
  have h5 := key 5
  rw [hy5, one_mul, inv_one, mul_one] at h5
  have hz5 : z ^ 5 = 1 := by
    have := congrArg (u⁻¹ * ·) h5
    simp only [inv_mul_cancel, inv_mul_cancel_left] at this
    exact inv_eq_one.1 this.symm
  have hz2 : z * z = 1 := hV₁ _ hu
  have hz1 : z = 1 := by
    calc z = z ^ 5 * (z * z)⁻¹ * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz5, hz2]; group
  rw [hyu, hz1, inv_one, mul_one]

section Fix

variable [Finite G] {T L V H K : Subgroup G} [IsMulCommutative ↥V]


theorem card_fix_le_mul {W : Type*} [Group W] [Finite W] (hW : ∀ a b : W, a * b = b * a)
    {A B : Subgroup W} (hAB : A ⊓ B = ⊥) (hsup : A ⊔ B = ⊤) {S : Subgroup (MulAut W)}
    (hSA : ∀ f ∈ S, ∀ a ∈ A, f a ∈ A) (hSB : ∀ f ∈ S, ∀ b ∈ B, f b ∈ B) :
    Nat.card {w : W // ∀ f ∈ S, f w = w} ≤
      Nat.card {a : ↥A // ∀ f ∈ S, f (a : W) = a} *
        Nat.card {b : ↥B // ∀ f ∈ S, f (b : W) = b} := by
  have hBn : B.Normal := ⟨fun n hn g => by rw [hW g n, mul_inv_cancel_right]; exact hn⟩
  have hdec : ∀ w : W, ∃ a ∈ A, ∃ b ∈ B, a * b = w := fun w =>
    Subgroup.mem_sup_of_normal_right.1 (hsup ▸ Subgroup.mem_top w)
  choose da hda db hdb hd using hdec
  have huniq : ∀ a ∈ A, ∀ b ∈ B, ∀ a' ∈ A, ∀ b' ∈ B, a * b = a' * b' → a = a' ∧ b = b' := by
    intro a ha b hb a' ha' b' hb' he
    have h1 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [he]
        _ = b' * b⁻¹ := by group
    have h2 : a'⁻¹ * a ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem ha') ha, h1 ▸ B.mul_mem hb' (B.inv_mem hb)⟩
    rw [hAB, Subgroup.mem_bot] at h2
    have ha'' : a = a' := by
      calc a = a' * (a'⁻¹ * a) := by group
        _ = a' := by rw [h2, mul_one]
    refine ⟨ha'', ?_⟩
    rw [ha''] at he
    exact mul_left_cancel he
  have hfix : ∀ w : W, (∀ f ∈ S, f w = w) →
      (∀ f ∈ S, f (da w) = da w) ∧ ∀ f ∈ S, f (db w) = db w := by
    intro w hw
    have key : ∀ f ∈ S, f (da w) = da w ∧ f (db w) = db w := by
      intro f hf
      have h1 : f (da w) * f (db w) = da w * db w := by
        rw [← map_mul, hd, hw f hf]
      exact huniq _ (hSA f hf _ (hda w)) _ (hSB f hf _ (hdb w)) _ (hda w) _ (hdb w) h1
    exact ⟨fun f hf => (key f hf).1, fun f hf => (key f hf).2⟩
  let φ : {w : W // ∀ f ∈ S, f w = w} → {a : ↥A // ∀ f ∈ S, f (a : W) = a} ×
      {b : ↥B // ∀ f ∈ S, f (b : W) = b} := fun w =>
    (⟨⟨da w.1, hda w.1⟩, (hfix w.1 w.2).1⟩, ⟨⟨db w.1, hdb w.1⟩, (hfix w.1 w.2).2⟩)
  have hinj : Function.Injective φ := by
    rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
    have h1 : da w = da w' := congrArg (fun p => ((p.1 : ↥A) : W)) h
    have h2 : db w = db w' := congrArg (fun p => ((p.2 : ↥B) : W)) h
    apply Subtype.ext
    show w = w'
    rw [← hd w, ← hd w', h1, h2]
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective φ hinj

theorem fix5_of_normalizes (F : Frame126 T L V) (h : HypF91 T V L F.V1 F.V5 H)
    {Ss : Subgroup (S126.HStar H)} (hST : Ss ≤ S126.star H T)
    (hMN : S126.star H (Subgroup.normalizer (L : Set G) ⊓ H) ≤
      Subgroup.normalizer (Ss : Set (S126.HStar H)))
    {s : S126.HStar H} (hs : s ∈ Ss) : Fix5 F.V1 F.V5 H (psiH h s) := by
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans h.reduced.2.1
  have hUN : conjClosure F.V5 H ≤ N1 F.V1 :=
    h.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 H).trans (le_N1 h))
  have hVN : F.V5 ≤ N1 F.V1 := (le_conjClosure F.V5 H).trans hUN
  have hQT : pCoreOf 2 H ≤ T := F7.isSylowTwoOf_pCoreOf_le h.sylow_H
  have hconjT : ∀ l ∈ Li L F.V1, ∀ x : ↥H, (x : G) ∈ T →
      (QuotientGroup.mk x : S126.HStar H) ∈ Ss → l * x * l⁻¹ * (x : G)⁻¹ ∈ T := by
    intro l hl x hxT hx
    have hlH : l ∈ H := h.L₁T_le_H (Subgroup.mem_sup_left hl)
    have hlM : (QuotientGroup.mk ⟨l, hlH⟩ : S126.HStar H) ∈
        S126.star H (Subgroup.normalizer (L : Set G) ⊓ H) :=
      ⟨⟨l, hlH⟩, Subgroup.mem_subgroupOf.2 ⟨Subgroup.le_normalizer (L1_le_L hl), hlH⟩, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 (hMN hlM) _).1 hx
    obtain ⟨y, hyT, hy⟩ := hST h1
    have hy' : (QuotientGroup.mk y : S126.HStar H) =
        QuotientGroup.mk (⟨l, hlH⟩ * x * ⟨l, hlH⟩⁻¹ : ↥H) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact hy
    have h2 := hQT (mem_pCoreOf_of_mk_eq hy')
    have h3 : l * x * l⁻¹ ∈ T := by
      have := T.mul_mem (Subgroup.mem_subgroupOf.1 hyT) h2
      simpa [mul_assoc] using this
    exact T.mul_mem h3 (T.inv_mem hxT)
  obtain ⟨x, hxT, rfl⟩ := hST hs
  have hxT' : (x : G) ∈ T := Subgroup.mem_subgroupOf.1 hxT
  show Fix5 F.V1 F.V5 H (thetaH h x)
  rw [fix5_thetaH_iff h x hVN]
  obtain ⟨σ, -, hσ⟩ := actsAs_of_mem_T F hxT'
  have hE : σ ∈ E16 :=
    mem_E16_of_conj F hTV hxT' (fun l hl _ => hconjT l hl x hxT' hs) hσ
  have hc := mem_centralizerMod_of_E16 (hTV hxT') (h.T_normalizes_V₁ hxT') hσ hE
  intro v hv
  have hvV : v ∈ V := h.Vp_le_V hv
  have key : ∀ a ∈ V, a * v⁻¹ ∈ F.V1 → a⁻¹ * v ∈ F.V1 := fun a haV ha => by
    have e : a⁻¹ * v = (a * v⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
      exact S126L1b.comm_of_mem (V.inv_mem haV) hvV
    rw [e]
    exact F.V1.inv_mem ha
  exact key _ (conj_mem (hTV hxT') ⟨v, hvV⟩) (hc.2.2 v hv)

end Fix

end CFSG.Quasithin.H13.L1232
