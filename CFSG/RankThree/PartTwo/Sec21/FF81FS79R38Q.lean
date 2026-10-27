module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R38Frame

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

namespace R38K

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

noncomputable abbrev Zsub (S : Std b t b₁ b₂ J) (A₁ : Subgroup J6.S6) : Subgroup H :=
  O1 S A₁ ⊔ Asub S A₁

noncomputable abbrev Jp (S : Std b t b₁ b₂ J) (J₁ : Subgroup J6.S6) : Subgroup H := J₁.map S.ι

section ZLemmas

variable {S : Std b t b₁ b₂ J} {A₁ : Subgroup J6.S6} {c₀ : J6.S6} {J₁ : Subgroup J6.S6}

theorem mem_Zsub_iff {z : H} :
    z ∈ Zsub S A₁ ↔ ∃ o ∈ O1 S A₁, ∃ a ∈ Asub S A₁, o * a = z := by
  have hcomm : ∀ o ∈ O1 S A₁, ∀ a ∈ Asub S A₁, Commute o a := fun o ho a ha =>
    mem_C1_iff.mp (L14.Opp_le 2 _ ho) a ha
  exact CFSG.mem_sup_of_commute hcomm

theorem O1_inf_Asub (Fr : Frame A₁ c₀ J₁) : O1 S A₁ ⊓ Asub S A₁ = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  rintro x ⟨hxO, hxA⟩
  have hx2 : x ^ (2 ^ 1) = 1 := by
    rw [pow_one, pow_two]
    exact Asub_sq Fr x hxA
  exact Subgroup.mem_bot.mpr (eq_one_of_pow_prime_pow (L14.Opp_coprime 2 _) hxO hx2)

theorem Zsub_le_C1 (Fr : Frame A₁ c₀ J₁) : Zsub S A₁ ≤ C1 S A₁ :=
  sup_le (L14.Opp_le 2 _) (Asub_le_C1 Fr)

theorem Zsub_le_Nor (Fr : Frame A₁ c₀ J₁) : Zsub S A₁ ≤ Nor (Asub S A₁) :=
  (Zsub_le_C1 Fr).trans C1_le_Nor

theorem Zsub_norm {g z : H} (hg : g ∈ Nor (Asub S A₁)) (hz : z ∈ Zsub S A₁) :
    g * z * g⁻¹ ∈ Zsub S A₁ := by
  obtain ⟨o, ho, a, ha, rfl⟩ := mem_Zsub_iff.mp hz
  have e : g * (o * a) * g⁻¹ = (g * o * g⁻¹) * (g * a * g⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem_sup (Nor_conj_O1 hg ho) ((Subgroup.mem_normalizer_iff.mp hg a).mp ha)

theorem Zsub_cop (Fr : Frame A₁ c₀ J₁) (hcop : Nat.Coprime 3 (Nat.card (O1 S A₁))) :
    Nat.Coprime 3 (Nat.card (Zsub S A₁)) := by
  have hcomm : ∀ o ∈ O1 S A₁, ∀ a ∈ Asub S A₁, Commute o a := fun o ho a ha =>
    mem_C1_iff.mp (L14.Opp_le 2 _ ho) a ha
  rw [CFSG.card_sup_eq_mul_of_commute _ _ hcomm (O1_inf_Asub Fr)]
  have hA2 : IsPGroup 2 (Asub S A₁) := by
    intro x
    refine ⟨1, ?_⟩
    have h1 : (x : H) * (x : H) = 1 := Asub_sq (S := S) Fr (x : H) x.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, pow_two]
    exact h1
  obtain ⟨n, hn⟩ := hA2.exists_card_eq
  rw [hn]
  exact Nat.Coprime.mul_right hcop (Nat.Coprime.pow_right n (by norm_num))

theorem not_mem_of_orderOf_three {Z : Subgroup H} (hZ : Nat.Coprime 3 (Nat.card Z)) {x : H}
    (hx : orderOf x = 3) : x ∉ Z := by
  intro hxZ
  have hx3 : x ^ (3 ^ 1) = 1 := by
    rw [pow_one, ← hx]
    exact pow_orderOf_eq_one x
  have := eq_one_of_pow_prime_pow hZ hxZ hx3
  rw [this, orderOf_one] at hx
  omega

theorem Zsub_inf_J (Fr : Frame A₁ c₀ J₁) {x : H} (hxJ : x ∈ J) (hxZ : x ∈ Zsub S A₁) :
    x ∈ Asub S A₁ := by
  obtain ⟨o, ho, a, ha, rfl⟩ := mem_Zsub_iff.mp hxZ
  have hoJ : o ∈ J := by
    have := J.mul_mem hxJ (J.inv_mem (Asub_le_J ha))
    simpa using this
  have hoA : o ∈ Asub S A₁ := C1_inf_J Fr hoJ (L14.Opp_le 2 _ ho)
  have : o ∈ O1 S A₁ ⊓ Asub S A₁ := ⟨ho, hoA⟩
  rw [O1_inf_Asub Fr, Subgroup.mem_bot] at this
  rw [this, one_mul]
  exact ha

theorem t_not_mem_Zsub (Fr : Frame A₁ c₀ J₁) : t ∉ Zsub S A₁ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro htZ
  have hA := S.hyp
  obtain ⟨o, ho, a, ha, hoa⟩ := mem_Zsub_iff.mp htZ
  have hcomm : o * a = a * o := mem_C1_iff.mp (L14.Opp_le 2 _ ho) a ha
  have ha2 : a * a = 1 := Asub_sq Fr a ha
  have e : (o * a) * (o * a) = o * o * (a * a) := by
    calc (o * a) * (o * a) = o * (a * o) * a := by group
      _ = o * (o * a) * a := by rw [← hcomm]
      _ = o * o * (a * a) := by group
  have ho2 : o ^ (2 ^ 1) = 1 := by
    have h1 : t * t = 1 := hA.t_sq
    rw [← hoa, e, ha2, mul_one] at h1
    rw [pow_one, pow_two]
    exact h1
  have ho1 : o = 1 := eq_one_of_pow_prime_pow (L14.Opp_coprime 2 _) ho ho2
  rw [ho1, one_mul] at hoa
  exact hA.t_not_mem_J (hoa ▸ Asub_le_J ha)

end ZLemmas

section JpLemmas

variable {S : Std b t b₁ b₂ J} {A₁ : Subgroup J6.S6} {c₀ : J6.S6} {J₁ : Subgroup J6.S6}

theorem Jp_le_J : Jp S J₁ ≤ J := by
  rintro _ ⟨s, -, rfl⟩
  exact S.ι_mem s

theorem Jp_le_Nor (Fr : Frame A₁ c₀ J₁) {x : H} (hx : x ∈ Jp S J₁) : x ∈ Nor (Asub S A₁) := by
  obtain ⟨s, hs, rfl⟩ := hx
  refine Subgroup.mem_normalizer_fintype fun a ha => ?_
  obtain ⟨u, hu, rfl⟩ := ha
  rw [← map_mul, ← map_inv, ← map_mul]
  exact ⟨_, Fr.norm s hs u hu, rfl⟩

theorem ι_c₀_mem_Jp (Fr : Frame A₁ c₀ J₁) : S.ι c₀ ∈ Jp S J₁ := ⟨c₀, Fr.c_mem, rfl⟩

theorem Jp_iso (Fr : Frame A₁ c₀ J₁) : Nonempty (↥(Jp S J₁) ≃* Perm (Fin 3)) := by
  obtain ⟨e⟩ := Fr.iso
  exact ⟨(Subgroup.equivMapOfInjective J₁ S.ι S.ι_injective).symm.trans e⟩

theorem ι_c₀_pow_three (Fr : Frame A₁ c₀ J₁) : S.ι c₀ ^ 3 = 1 := by
  rw [← map_pow, Fr.c_pow, map_one]

theorem ι_c₀_ne_one (Fr : Frame A₁ c₀ J₁) : S.ι c₀ ≠ 1 := fun h =>
  Fr.c_ne (S.ι_injective (h.trans (map_one S.ι).symm))

theorem ι_c₀_orderOf (Fr : Frame A₁ c₀ J₁) : orderOf (S.ι c₀) = 3 :=
  orderOf_eq_prime (ι_c₀_pow_three Fr) (ι_c₀_ne_one Fr)

theorem Jp_inf_Zsub (Fr : Frame A₁ c₀ J₁) : Jp S J₁ ⊓ Zsub S A₁ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxJp, hxZ⟩
  have hxA := Zsub_inf_J Fr (Jp_le_J hxJp) hxZ
  obtain ⟨s, hsJ₁, rfl⟩ := hxJp
  obtain ⟨s', hs'A, hss'⟩ := hxA
  have h1 : s' = s := S.ι_injective hss'
  subst h1
  have h2 : s' = 1 := Fr.inf s' hsJ₁ hs'A
  subst h2
  simp

theorem decomp_A (Fr : Frame A₁ c₀ J₁) {n : H} (hn : n ∈ Nor (Subgroup.zpowers b))
    (hnA : n ∈ Nor (Asub S A₁)) :
    ∃ κ ∈ Opp 3 (Nor (Subgroup.zpowers b)), ∃ y ∈ Subgroup.closure ({b, t} : Set H),
      ∃ a ∈ Asub S A₁, ∃ s ∈ Jp S J₁, n = κ * y * (a * s) := by
  obtain ⟨κ, hκ, y, hy, j, hj, rfl⟩ := S.hyp.nor_decomp hn
  obtain ⟨σ, rfl⟩ := S.exists_ι hj
  have hσ : ∀ s ∈ A₁, σ * s * σ⁻¹ ∈ A₁ := by
    intro s hs
    have h1 : (κ * y * S.ι σ) * S.ι s * (κ * y * S.ι σ)⁻¹ ∈ Asub S A₁ :=
      (Subgroup.mem_normalizer_iff.mp hnA _).mp (ι_mem_Asub hs)
    rw [S.hyp.conj_eq_of_decomp hκ hy (S.ι_mem σ) (S.ι_mem s)] at h1
    obtain ⟨u, hu, hue⟩ := h1
    have : u = σ * s * σ⁻¹ := S.ι_injective (by rw [hue, map_mul, map_mul, map_inv])
    rwa [← this]
  obtain ⟨a₁, ha₁, s₁, hs₁, hσe⟩ := Fr.nor σ hσ
  refine ⟨κ, hκ, y, hy, S.ι a₁, ι_mem_Asub ha₁, S.ι s₁, ⟨s₁, hs₁, rfl⟩, ?_⟩
  rw [hσe, map_mul]

end JpLemmas

section Fields

variable {S : Std b t b₁ b₂ J} {A₁ : Subgroup J6.S6} {c₀ : J6.S6} {J₁ : Subgroup J6.S6}

theorem conj_mem_Asub {g x : H} (hg : g ∈ Nor (Asub S A₁)) (hx : x ∈ Asub S A₁) :
    g * x * g⁻¹ ∈ Asub S A₁ := (Subgroup.mem_normalizer_iff.mp hg x).mp hx

theorem conj_inv_mem_Asub {g x : H} (hg : g ∈ Nor (Asub S A₁)) (hx : x ∈ Asub S A₁) :
    g⁻¹ * x * g ∈ Asub S A₁ := by
  have := (Subgroup.mem_normalizer_iff.mp ((Nor _).inv_mem hg) x).mp hx
  simpa using this

theorem Asub_le_Zsub : Asub S A₁ ≤ Zsub S A₁ := le_sup_right

theorem b_mem_Nor (Fr : Frame A₁ c₀ J₁) : b ∈ Nor (Asub S A₁) := C1_le_Nor b_mem_C1

theorem comm_aux (Fr : Frame A₁ c₀ J₁) {w z : H} (a : H) (hw : w ∈ Nor (Asub S A₁))
    (hz : z ∈ Zsub S A₁) (ha : a ∈ Asub S A₁) :
    (w⁻¹ * z * w) * a * z⁻¹ ∈ Zsub S A₁ := by
  have h1 : w⁻¹ * z * w ∈ Zsub S A₁ := by
    have := Zsub_norm ((Nor _).inv_mem hw) hz
    simpa using this
  exact (Zsub S A₁).mul_mem ((Zsub S A₁).mul_mem h1 (Asub_le_Zsub ha)) ((Zsub S A₁).inv_mem hz)

theorem q_N_J (Fr : Frame A₁ c₀ J₁) (hcop : Nat.Coprime 3 (Nat.card (O1 S A₁))) {g : H}
    (hg : g ∈ Nor (Asub S A₁) ⊓ Nor (Subgroup.zpowers b ⊔ Zsub S A₁)) {j : H}
    (hj : j ∈ Jp S J₁) :
    ∃ j' ∈ Jp S J₁, ∃ z ∈ Zsub S A₁, g * j * g⁻¹ = j' * z := by
  have h := S.hyp
  obtain ⟨z', hz', n, hn, rfl⟩ := nor_sup_decomp_rel h.ord_b (b_mem_Nor Fr) (Zsub_le_Nor Fr)
    (fun _ hg' _ hz => Zsub_norm hg' hz) (Zsub_cop Fr hcop) hg.1 hg.2
  obtain ⟨κ, hκ, y, hy, a, ha, s, hs, rfl⟩ := decomp_A Fr hn.2 hn.1
  have hjJ : j ∈ J := Jp_le_J hj
  have e1 := h.conj_eq_of_decomp hκ hy (J.mul_mem (Asub_le_J ha) (Jp_le_J hs)) hjJ
  set w : H := s * j * s⁻¹ with hw
  have hwJp : w ∈ Jp S J₁ := (Jp S J₁).mul_mem ((Jp S J₁).mul_mem hs hj) ((Jp S J₁).inv_mem hs)
  have hwN : w ∈ Nor (Asub S A₁) := Jp_le_Nor Fr hwJp
  have ha₁ : (w⁻¹ * a * w) * a⁻¹ ∈ Asub S A₁ :=
    (Asub S A₁).mul_mem (by simpa using conj_mem_Asub ((Nor _).inv_mem hwN) ha)
      ((Asub S A₁).inv_mem ha)
  refine ⟨w, hwJp, (w⁻¹ * z' * w) * ((w⁻¹ * a * w) * a⁻¹) * z'⁻¹, ?_, ?_⟩
  · exact comm_aux Fr (z := z') ((w⁻¹ * a * w) * a⁻¹) hwN hz' ha₁
  · have e2 : z' * (κ * y * (a * s)) * j * (z' * (κ * y * (a * s)))⁻¹ =
        z' * ((κ * y * (a * s)) * j * (κ * y * (a * s))⁻¹) * z'⁻¹ := by group
    rw [e2, e1, hw]
    group

theorem q_struct_b (Fr : Frame A₁ c₀ J₁) (hcop : Nat.Coprime 3 (Nat.card (O1 S A₁))) :
    ∃ W : Subgroup H,
      W ≤ Nor (Asub S A₁) ⊓ Nor (Subgroup.zpowers b ⊔ Zsub S A₁) ∧
      Nat.Coprime 3 (Nat.card W) ∧
      (∀ g ∈ Nor (Asub S A₁) ⊓ Nor (Subgroup.zpowers b ⊔ Zsub S A₁), ∀ w ∈ W,
        ∃ w' ∈ W, ∃ z ∈ Zsub S A₁, g * w * g⁻¹ = w' * z) ∧
      (∀ g ∈ Nor (Asub S A₁) ⊓ Nor (Subgroup.zpowers b ⊔ Zsub S A₁), ∃ w ∈ W,
        ∃ y ∈ Subgroup.closure ({b, t} : Set H), ∃ j ∈ Jp S J₁, ∃ z ∈ Zsub S A₁,
          g = w * y * j * z) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := S.hyp
  have hKN : ∀ κ ∈ Opp 3 (Nor (Subgroup.zpowers b)), κ ∈ Nor (Asub S A₁) := fun κ hκ =>
    C1_le_Nor (K_le_C1 hκ)
  refine ⟨Opp 3 (Nor (Subgroup.zpowers b)), ?_, L14.Opp_coprime 3 _, ?_, ?_⟩
  · intro κ hκ
    refine ⟨hKN κ hκ, Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨L14.Opp_le 3 _ hκ, ?_⟩⟩
    exact Subgroup.mem_normalizer_fintype fun z hz => Zsub_norm (hKN κ hκ) hz
  · intro g hg w hw
    obtain ⟨z', hz', n, hn, rfl⟩ := nor_sup_decomp_rel h.ord_b (b_mem_Nor Fr) (Zsub_le_Nor Fr)
      (fun _ hg' _ hz => Zsub_norm hg' hz) (Zsub_cop Fr hcop) hg.1 hg.2
    have hw' : n * w * n⁻¹ ∈ Opp 3 (Nor (Subgroup.zpowers b)) := L14.Opp_conj_mem hn.2 hw
    refine ⟨n * w * n⁻¹, hw', ((n * w * n⁻¹)⁻¹ * z' * (n * w * n⁻¹)) * 1 * z'⁻¹,
      comm_aux Fr 1 (hKN _ hw') hz' (Asub S A₁).one_mem, ?_⟩
    group
  · intro g hg
    obtain ⟨z', hz', n, hn, rfl⟩ := nor_sup_decomp_rel h.ord_b (b_mem_Nor Fr) (Zsub_le_Nor Fr)
      (fun _ hg' _ hz => Zsub_norm hg' hz) (Zsub_cop Fr hcop) hg.1 hg.2
    obtain ⟨κ, hκ, y, hy, a, ha, s, hs, rfl⟩ := decomp_A Fr hn.2 hn.1
    have hsN : s ∈ Nor (Asub S A₁) := Jp_le_Nor Fr hs
    have hz₂ : (κ * y * (a * s))⁻¹ * z' * (κ * y * (a * s)) ∈ Zsub S A₁ := by
      have := Zsub_norm ((Nor _).inv_mem hn.1) hz'
      simpa using this
    refine ⟨κ, hκ, y, hy, s, hs, (s⁻¹ * a * s) * ((κ * y * (a * s))⁻¹ * z' * (κ * y * (a * s))),
      (Zsub S A₁).mul_mem (Asub_le_Zsub (conj_inv_mem_Asub hsN ha)) hz₂, ?_⟩
    group

theorem J_inf_Q_eq_one (Fr : Frame A₁ c₀ J₁) {x : H} (hxJ : x ∈ J)
    (hxQ : x ∈ Opp 3 (Nor (Subgroup.zpowers (S.ι c₀)))) : x = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hx1
  set c : H := S.ι c₀ with hc
  have hc3 : c ^ 3 = 1 := ι_c₀_pow_three Fr
  have hc1 : c ≠ 1 := ι_c₀_ne_one Fr
  have hxN : x ∈ Nor (Subgroup.zpowers c) := L14.Opp_le 3 _ hxQ
  have hxcmem : x * c * x⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hxN c).mp (Subgroup.mem_zpowers c)
  have hxc : x * c * x⁻¹ = c :=
    conj_eq_of_coprime_normal (X := Nor (Subgroup.zpowers c))
      (Q := Opp 3 (Nor (Subgroup.zpowers c))) (fun g hg q hq => L14.Opp_conj_mem hg hq)
      (L14.Opp_coprime 3 _) (mem_Nor_self c) hc3 hc1 hxQ hxcmem
  obtain ⟨ξ, rfl⟩ := S.exists_ι hxJ
  have hξc : ξ * c₀ = c₀ * ξ := by
    apply S.ι_injective
    rw [map_mul, map_mul]
    calc S.ι ξ * c = (S.ι ξ * c * (S.ι ξ)⁻¹) * S.ι ξ := by group
      _ = c * S.ι ξ := by rw [hxc]
  have hξ1 : ξ ≠ 1 := fun h1 => hx1 (by rw [h1, map_one])
  obtain ⟨j₀, hj₀, hne, h3⟩ := Fr.f3 ξ hξc hξ1
  have hu : S.ι j₀ ∈ Nor (Subgroup.zpowers c) := by
    refine mem_Nor_zpowers_of_conj ?_
    have : S.ι j₀ * c * (S.ι j₀)⁻¹ = S.ι (j₀ * c₀ * j₀⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [this]
    rcases hj₀ with h1 | h1
    · rw [h1]
      exact Subgroup.mem_zpowers _
    · rw [h1, map_inv]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  have hxu : S.ι j₀ * S.ι ξ * (S.ι j₀)⁻¹ ∈ Opp 3 (Nor (Subgroup.zpowers c)) :=
    L14.Opp_conj_mem hu hxQ
  have hy : S.ι ξ * (S.ι j₀ * S.ι ξ * (S.ι j₀)⁻¹) ∈ Opp 3 (Nor (Subgroup.zpowers c)) :=
    (Opp 3 (Nor (Subgroup.zpowers c))).mul_mem hxQ hxu
  have hyeq : S.ι ξ * (S.ι j₀ * S.ι ξ * (S.ι j₀)⁻¹) = S.ι (ξ * (j₀ * ξ * j₀⁻¹)) := by
    rw [map_mul, map_mul, map_mul, map_inv]
  rw [hyeq] at hy
  have hy3 : S.ι (ξ * (j₀ * ξ * j₀⁻¹)) ^ 3 = 1 := by
    rw [← map_pow, h3, map_one]
  have := eq_one_of_mem_coprime_of_pow_three (L14.Opp_coprime 3 _) hy hy3
  exact hne (S.ι_injective (this.trans (map_one S.ι).symm))

theorem key_nor (Fr : Frame A₁ c₀ J₁) {n₀ q n₁ : H} (hn₀ : n₀ ∈ Nor (Asub S A₁))
    (hq : q ∈ Opp 3 (Nor (Subgroup.zpowers (S.ι c₀)))) (hn₁b : n₁ ∈ Nor (Subgroup.zpowers b))
    (hn₁c : n₁ ∈ Nor (Subgroup.zpowers (S.ι c₀))) (e : n₀ = q * n₁) : n₁ ∈ Nor (Asub S A₁) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := S.hyp
  set c : H := S.ι c₀ with hc
  have hc3 : c ^ 3 = 1 := ι_c₀_pow_three Fr
  have hc1 : c ≠ 1 := ι_c₀_ne_one Fr
  have hcJ : c ∈ J := S.ι_mem c₀
  obtain ⟨κ, hκ, y, hy, j₁, hj₁, rfl⟩ := h.nor_decomp hn₁b
  obtain ⟨σ, rfl⟩ := S.exists_ι hj₁
  have hconj : ∀ x : H, x ∈ J → (κ * y * S.ι σ) * x * (κ * y * S.ι σ)⁻¹ =
      S.ι σ * x * (S.ι σ)⁻¹ := fun x hx => h.conj_eq_of_decomp hκ hy (S.ι_mem σ) hx
  have hσc : σ * c₀ * σ⁻¹ = c₀ ∨ σ * c₀ * σ⁻¹ = c₀⁻¹ := by
    have h1 : S.ι σ * c * (S.ι σ)⁻¹ ∈ Subgroup.zpowers c := by
      rw [← hconj c hcJ]
      exact (Subgroup.mem_normalizer_iff.mp hn₁c c).mp (Subgroup.mem_zpowers c)
    have h2 : S.ι σ * c * (S.ι σ)⁻¹ ≠ 1 := by
      intro h1'
      apply hc1
      calc c = (S.ι σ)⁻¹ * (S.ι σ * c * (S.ι σ)⁻¹) * S.ι σ := by group
        _ = 1 := by rw [h1']; group
    have e1 : S.ι σ * c * (S.ι σ)⁻¹ = S.ι (σ * c₀ * σ⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rcases eq_or_inv_of_mem_zpowers_of_pow_three hc3 hc1 h1 h2 with h3 | h3
    · left
      exact S.ι_injective (by rw [← e1, h3])
    · right
      exact S.ι_injective (by rw [← e1, h3, map_inv])
  have hstep : ∀ e' ∈ A₁, e' * c₀ = c₀ * e' → σ * e' * σ⁻¹ ∈ A₁ := by
    intro e' he' hec
    set e'' : H := S.ι (σ * e' * σ⁻¹) with he''
    have hcomm0 : (σ * e' * σ⁻¹) * c₀ = c₀ * (σ * e' * σ⁻¹) := by
      have hcσ : (σ * e' * σ⁻¹) * (σ * c₀ * σ⁻¹) = (σ * c₀ * σ⁻¹) * (σ * e' * σ⁻¹) := by
        calc (σ * e' * σ⁻¹) * (σ * c₀ * σ⁻¹) = σ * (e' * c₀) * σ⁻¹ := by group
          _ = σ * (c₀ * e') * σ⁻¹ := by rw [hec]
          _ = (σ * c₀ * σ⁻¹) * (σ * e' * σ⁻¹) := by group
      rcases hσc with h1 | h1
      · rw [h1] at hcσ
        exact hcσ
      · rw [h1] at hcσ
        have := (Commute.inv_right (show Commute (σ * e' * σ⁻¹) c₀⁻¹ from hcσ)).eq
        simpa using this
    have he''c : e'' * c = c * e'' := by
      rw [he'', hc, ← map_mul, ← map_mul, hcomm0]
    have he''J : e'' ∈ J := S.ι_mem _
    have he''N : e'' ∈ Nor (Subgroup.zpowers c) := mem_Nor_zpowers_of_comm he''c
    have h1 : q * e'' * q⁻¹ ∈ Asub S A₁ := by
      have h2 : n₀ * S.ι e' * n₀⁻¹ ∈ Asub S A₁ :=
        conj_mem_Asub hn₀ (ι_mem_Asub he')
      have h3 : n₀ * S.ι e' * n₀⁻¹ = q * e'' * q⁻¹ := by
        have h4 : n₀ * S.ι e' * n₀⁻¹ =
            q * ((κ * y * S.ι σ) * S.ι e' * (κ * y * S.ι σ)⁻¹) * q⁻¹ := by
          rw [e]
          group
        rw [h4, hconj _ (S.ι_mem e'), he'']
        simp only [map_mul, map_inv]
      rwa [h3] at h2
    have hXJ : (q * e'' * q⁻¹) * e''⁻¹ ∈ J :=
      J.mul_mem (Asub_le_J h1) (J.inv_mem he''J)
    have hXQ : (q * e'' * q⁻¹) * e''⁻¹ ∈ Opp 3 (Nor (Subgroup.zpowers c)) := by
      have : (q * e'' * q⁻¹) * e''⁻¹ = q * (e'' * q⁻¹ * e''⁻¹) := by group
      rw [this]
      exact (Opp 3 (Nor (Subgroup.zpowers c))).mul_mem hq
        (L14.Opp_conj_mem he''N ((Opp 3 (Nor (Subgroup.zpowers c))).inv_mem hq))
    have hX1 := J_inf_Q_eq_one Fr hXJ hXQ
    have hqe : q * e'' * q⁻¹ = e'' := mul_inv_eq_one.mp hX1
    rw [hqe] at h1
    obtain ⟨u, hu, hue⟩ := h1
    have : u = σ * e' * σ⁻¹ := S.ι_injective hue
    rwa [← this]
  have hall := Fr.f4 σ hσc hstep
  refine Subgroup.mem_normalizer_fintype fun a ha => ?_
  obtain ⟨s, hs, rfl⟩ := ha
  rw [hconj _ (S.ι_mem s)]
  exact ⟨σ * s * σ⁻¹, hall s hs, by simp only [map_mul, map_inv]⟩

theorem Zsub_mem_Nor {n : H} (hn : n ∈ Nor (Asub S A₁)) : n ∈ Nor (Zsub S A₁) :=
  Subgroup.mem_normalizer_fintype fun _ hz => Zsub_norm hn hz

theorem q_struct_c (Fr : Frame A₁ c₀ J₁) (hcop : Nat.Coprime 3 (Nat.card (O1 S A₁)))
    (hC₁ : CtlEq b (S.ι c₀)) :
    ∃ Wc : Subgroup H,
      Wc ≤ Nor (Asub S A₁) ⊓ Nor (Subgroup.zpowers (S.ι c₀) ⊔ Zsub S A₁) ∧
      Nat.Coprime 3 (Nat.card Wc) ∧
      (∀ g ∈ Nor (Asub S A₁) ⊓ Nor (Subgroup.zpowers (S.ι c₀) ⊔ Zsub S A₁), ∀ w ∈ Wc,
        ∃ w' ∈ Wc, ∃ z ∈ Zsub S A₁, g * w * g⁻¹ = w' * z) ∧
      (∀ g ∈ Nor (Asub S A₁) ⊓ Nor (Subgroup.zpowers (S.ι c₀) ⊔ Zsub S A₁), ∃ w ∈ Wc,
        ∃ n ∈ Nor (Asub S A₁) ⊓ Nor (Subgroup.zpowers (S.ι c₀) ⊔ Zsub S A₁) ⊓
          Nor (Subgroup.zpowers b ⊔ Zsub S A₁), ∃ z ∈ Zsub S A₁, g = w * n * z) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := S.hyp
  have hcN : S.ι c₀ ∈ Nor (Asub S A₁) := Jp_le_Nor Fr (ι_c₀_mem_Jp Fr)
  have hfr : ∀ g ∈ Nor (Asub S A₁) ⊓ Nor (Subgroup.zpowers (S.ι c₀) ⊔ Zsub S A₁),
      ∃ z ∈ Zsub S A₁, ∃ n ∈ Nor (Asub S A₁) ⊓ Nor (Subgroup.zpowers (S.ι c₀)), g = z * n :=
    fun g hg => nor_sup_decomp_rel (ι_c₀_orderOf Fr) hcN (Zsub_le_Nor Fr)
      (fun _ hg' _ hz => Zsub_norm hg' hz) (Zsub_cop Fr hcop) hg.1 hg.2
  refine ⟨Opp 3 (Nor (Subgroup.zpowers (S.ι c₀))) ⊓ Nor (Asub S A₁), ?_, ?_, ?_, ?_⟩
  · intro w hw
    exact ⟨hw.2, Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨L14.Opp_le 3 _ hw.1, Zsub_mem_Nor hw.2⟩⟩
  · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (L14.Opp_coprime 3 _)
  · intro g hg w hw
    obtain ⟨z₀, hz₀, n₀, hn₀, rfl⟩ := hfr g hg
    have hw' : n₀ * w * n₀⁻¹ ∈ Opp 3 (Nor (Subgroup.zpowers (S.ι c₀))) ⊓ Nor (Asub S A₁) :=
      ⟨L14.Opp_conj_mem hn₀.2 hw.1,
        (Nor _).mul_mem ((Nor _).mul_mem hn₀.1 hw.2) ((Nor _).inv_mem hn₀.1)⟩
    refine ⟨n₀ * w * n₀⁻¹, hw', ((n₀ * w * n₀⁻¹)⁻¹ * z₀ * (n₀ * w * n₀⁻¹)) * 1 * z₀⁻¹,
      comm_aux Fr 1 hw'.2 hz₀ (Asub S A₁).one_mem, ?_⟩
    group
  · intro g hg
    obtain ⟨z₀, hz₀, n₀, hn₀, rfl⟩ := hfr g hg
    have hn₀N : n₀ ∈ setMul (Opp 3 (Nor (Subgroup.zpowers (S.ι c₀))))
        (Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers (S.ι c₀))) := by
      unfold CtlEq at hC₁
      rw [hC₁]
      exact hn₀.2
    obtain ⟨q, hq, n₁, hn₁, e⟩ := hn₀N
    have hn₁A : n₁ ∈ Nor (Asub S A₁) := key_nor Fr hn₀.1 hq hn₁.1 hn₁.2 e
    have hqA : q ∈ Nor (Asub S A₁) := by
      have : q = n₀ * n₁⁻¹ := by rw [e]; group
      rw [this]
      exact (Nor _).mul_mem hn₀.1 ((Nor _).inv_mem hn₁A)
    have hz : (q * n₁)⁻¹ * z₀ * (q * n₁) ∈ Zsub S A₁ := by
      have := Zsub_norm ((Nor _).inv_mem hn₀.1) hz₀
      rw [e] at this
      simpa using this
    refine ⟨q, ⟨hq, hqA⟩, n₁, ⟨⟨hn₁A, Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨hn₁.2, Zsub_mem_Nor hn₁A⟩⟩, Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨hn₁.1, Zsub_mem_Nor hn₁A⟩⟩, (q * n₁)⁻¹ * z₀ * (q * n₁), hz, ?_⟩
    rw [e]
    group

theorem perm3_two_pow (X : Perm (Fin 3)) (h : ∃ k : ℕ, X ^ (2 ^ k) = 1) : X ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := h
  have hcases : ∀ Y : Perm (Fin 3), Y ^ 2 = 1 ∨ Y ^ 3 = 1 := by decide
  rcases hcases X with h2 | h3
  · exact h2
  · have h1 : orderOf X ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have h2 : orderOf X ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have : orderOf X = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (by norm_num)) h1 h2
    have hX1 : X = 1 := orderOf_eq_one_iff.mp this
    rw [hX1, one_pow]

theorem perm3_prod_ne : ∀ G X : Perm (Fin 3), G ^ 3 = 1 → G ≠ 1 → X ^ 2 = 1 → X ≠ 1 →
    ((G * X * G⁻¹) * X) ^ 2 ≠ 1 := by decide +kernel

theorem Jp_two_trivial (Fr : Frame A₁ c₀ J₁) {P : Subgroup H} (hPJ : P ≤ Jp S J₁)
    (hP2 : IsPGroup 2 P) (hc : ∀ x ∈ P, S.ι c₀ * x * (S.ι c₀)⁻¹ ∈ P) : P = ⊥ := by
  obtain ⟨e⟩ := Jp_iso (S := S) Fr
  rw [eq_bot_iff]
  intro x hx
  by_contra hx1
  have hcJ : S.ι c₀ ∈ Jp S J₁ := ι_c₀_mem_Jp Fr
  set G : Perm (Fin 3) := e ⟨S.ι c₀, hcJ⟩ with hG
  set X : Perm (Fin 3) := e ⟨x, hPJ hx⟩ with hX
  have hG3 : G ^ 3 = 1 := by
    rw [hG, ← map_pow]
    have : (⟨S.ι c₀, hcJ⟩ : ↥(Jp S J₁)) ^ 3 = 1 := Subtype.ext (by simpa using ι_c₀_pow_three Fr)
    rw [this, map_one]
  have hG1 : G ≠ 1 := by
    intro h1
    have : (⟨S.ι c₀, hcJ⟩ : ↥(Jp S J₁)) = 1 := e.injective (h1.trans (map_one e).symm)
    exact ι_c₀_ne_one Fr (congrArg Subtype.val this)
  have hX1 : X ≠ 1 := by
    intro h1
    have : (⟨x, hPJ hx⟩ : ↥(Jp S J₁)) = 1 := e.injective (h1.trans (map_one e).symm)
    exact hx1 (congrArg Subtype.val this)
  have hX2 : X ^ 2 = 1 := by
    apply perm3_two_pow
    obtain ⟨k, hk⟩ := hP2 ⟨x, hx⟩
    refine ⟨k, ?_⟩
    rw [hX, ← map_pow]
    have : (⟨x, hPJ hx⟩ : ↥(Jp S J₁)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hy : (S.ι c₀ * x * (S.ι c₀)⁻¹) * x ∈ P := P.mul_mem (hc x hx) hx
  have hyJ : (S.ι c₀ * x * (S.ι c₀)⁻¹) * x ∈ Jp S J₁ := hPJ hy
  have hYe : e ⟨_, hyJ⟩ = (G * X * G⁻¹) * X := by
    have : (⟨_, hyJ⟩ : ↥(Jp S J₁)) = ⟨S.ι c₀, hcJ⟩ * ⟨x, hPJ hx⟩ * ⟨S.ι c₀, hcJ⟩⁻¹ * ⟨x, hPJ hx⟩ :=
      rfl
    rw [this, map_mul, map_mul, map_mul, map_inv]
  have hY2 : ((G * X * G⁻¹) * X) ^ 2 = 1 := by
    rw [← hYe]
    apply perm3_two_pow
    obtain ⟨k, hk⟩ := hP2 ⟨_, hy⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨_, hyJ⟩ : ↥(Jp S J₁)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  exact perm3_prod_ne G X hG3 hG1 hX2 hX1 hY2

theorem not_dvd_of_two_pow_mem {Z R : Subgroup H} (hZc : Nat.Coprime 3 (Nat.card Z))
    (hR2 : ∀ r ∈ R, ∃ k : ℕ, r ^ (2 ^ k) ∈ Z) : ¬ 3 ∣ Nat.card R := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hd
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) 3 hd
  have hrG : orderOf (r : H) = 3 := by rw [Subgroup.orderOf_coe]; exact hr
  obtain ⟨k, hk⟩ := hR2 (r : H) r.2
  have hr3 : (r : H) ^ 3 = 1 := by
    rw [← hrG]
    exact pow_orderOf_eq_one _
  have h4 : ∀ m : ℕ, (r : H) ^ (4 ^ m) = r := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, pow_mul, ih]
      calc (r : H) ^ 4 = (r : H) ^ 3 * (r : H) := by rw [pow_succ]
        _ = (r : H) := by rw [hr3, one_mul]
  have hrZ : (r : H) ∈ Z := by
    have e2 : (2 : ℕ) ^ k * 2 ^ k = 4 ^ k := by
      rw [← mul_pow]
      norm_num
    have e : ((r : H) ^ (2 ^ k)) ^ (2 ^ k) = (r : H) := by
      rw [← pow_mul, e2, h4 k]
    rw [← e]
    exact Z.pow_mem hk _
  exact not_mem_of_orderOf_three hZc hrG hrZ

theorem cen_two_mem_J (h : FS79Hyp b t b₁ b₂ J) {s : H} (hs : s ∈ Cen b) {m : ℕ}
    (hm : s ^ (2 ^ m) = 1) : s ∈ J := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb3 : b ^ 3 = 1 := by
    rw [← h.ord_b]
    exact pow_orderOf_eq_one b
  obtain ⟨κ, hκ, i, j, hj, rfl⟩ := cen_decomp h hs
  have hκb : κ * b = b * κ := Ctl34.K_comm_b h hκ
  have hκbi : Commute κ (b ^ i) := Commute.zpow_right (show Commute κ b from hκb) i
  have hκj : Commute κ j := h.K_comm_J hκ hj
  have hbij : Commute (b ^ i) j := by
    have : j * b = b * j := Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b hj)
    exact Commute.zpow_left (show Commute b j from this.symm) i
  have hc1 : Commute (κ * b ^ i) j := hκj.mul_left hbij
  have hpow : (κ * b ^ i * j) ^ (2 ^ m) = κ ^ (2 ^ m) * (b ^ i) ^ (2 ^ m) * j ^ (2 ^ m) := by
    rw [hc1.mul_pow, hκbi.mul_pow]
  rw [hpow] at hm
  have hbiY : (b ^ i) ^ (2 ^ m) ∈ Subgroup.closure ({b, t} : Set H) :=
    Subgroup.pow_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) i) _
  have hjJ : j ^ (2 ^ m) ∈ J := J.pow_mem hj _
  have hκN : κ ^ (2 ^ m) = ((b ^ i) ^ (2 ^ m) * j ^ (2 ^ m))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← mul_assoc]
    exact hm
  have hκmem : κ ^ (2 ^ m) ∈ Opp 3 (Nor (Subgroup.zpowers b)) ⊓
      (Subgroup.closure ({b, t} : Set H) ⊔ J) := by
    refine ⟨Subgroup.pow_mem _ hκ _, ?_⟩
    rw [hκN]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem_sup hbiY hjJ)
  rw [h.K_inf_M0, Subgroup.mem_bot] at hκmem
  have hκ1 : κ = 1 := eq_one_of_pow_prime_pow (Nat.coprime_two_left.mpr h.odd_K) hκ hκmem
  rw [hκ1, one_pow, one_mul] at hm
  have hbN : (b ^ i) ^ (2 ^ m) = (j ^ (2 ^ m))⁻¹ := eq_inv_of_mul_eq_one_left hm
  have hbmem : (b ^ i) ^ (2 ^ m) ∈ Subgroup.zpowers b ⊓ J := by
    refine ⟨Subgroup.pow_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i) _, ?_⟩
    rw [hbN]
    exact J.inv_mem hjJ
  rw [h.zpowers_inf_J, Subgroup.mem_bot] at hbmem
  have hbi1 : b ^ i = 1 := by
    have h1 : orderOf (b ^ i) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (pow_three_of_mem_zpowers hb3
        (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i))
    have h2 : orderOf (b ^ i) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hbmem
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right m (by norm_num)) h1 h2)
  rw [hκ1, hbi1, one_mul, one_mul]
  exact hj

theorem isPGroup_Asub (Fr : Frame A₁ c₀ J₁) : IsPGroup 2 (Asub S A₁) := by
  intro x
  refine ⟨1, ?_⟩
  have h1 : (x : H) * (x : H) = 1 := Asub_sq (S := S) Fr (x : H) x.2
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, pow_two]
  exact h1

theorem q_no2 (Fr : Frame A₁ c₀ J₁) (hcop : Nat.Coprime 3 (Nat.card (O1 S A₁)))
    (hC₁ : CtlEq b (S.ι c₀)) (hC₂ : CtlEq b (b * S.ι c₀)) (hC₃ : CtlEq b (b * (S.ι c₀)⁻¹))
    (hO₁ : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers (S.ι c₀))))))
    (hO₂ : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers (b * S.ι c₀))))))
    (hO₃ : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers (b * (S.ι c₀)⁻¹))))))
    {R : Subgroup H} (hRΓ : R ≤ Nor (Asub S A₁)) (hZR : Zsub S A₁ ≤ R)
    (hR2 : ∀ r ∈ R, ∃ k : ℕ, r ^ (2 ^ k) ∈ Zsub S A₁)
    (hb : b ∈ Nor R) (hc : S.ι c₀ ∈ Nor R) : R ≤ Zsub S A₁ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := S.hyp
  set c : H := S.ι c₀ with hcdef
  have hb3 : b ^ 3 = 1 := by
    rw [← h.ord_b]
    exact pow_orderOf_eq_one b
  have hc3 : c ^ 3 = 1 := ι_c₀_pow_three Fr
  have hbc : b * c = c * b := (S.ι_comm_b c₀).symm
  have hcJ : c ∈ J := S.ι_mem c₀
  have hdisj : Subgroup.zpowers b ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff, ← h.zpowers_inf_J]
    exact inf_le_inf_left _ (Subgroup.zpowers_le.mpr hcJ)
  have hR3 : ¬ 3 ∣ Nat.card R := not_dvd_of_two_pow_mem (Zsub_cop Fr hcop) hR2
  have hB3 : IsPGroup 3 (Subgroup.closure ({b, c} : Set H)) := isPGroup_closure_pair hbc hb3 hc3
  have hBR : Subgroup.closure ({b, c} : Set H) ≤ Nor R := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hb
    · exact hc
  obtain ⟨R₂, hR₂syl, -, hAR⟩ := CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime
    (q := 3) (r := 2) (A := Subgroup.closure ({b, c} : Set H)) (K := R) (P := ⊥)
    Nat.prime_three Nat.prime_two hB3 hBR hR3 bot_le IsPGroup.of_bot
    Subgroup.le_normalizer_of_normal
  have hR₂2 : IsPGroup 2 R₂ := CFSG.ABGLocalTools.IsSylowOf.isPGroup hR₂syl
  obtain ⟨hR₂R, -, hR₂idx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hR₂syl
  have hbR₂ : b ∈ Nor R₂ := hAR (Subgroup.subset_closure (by simp))
  have hcR₂ : c ∈ Nor R₂ := hAR (Subgroup.subset_closure (by simp))
  have hcen : ∀ x ∈ R₂, x * b = b * x :=
    le_cen_of_e9 h.ord_b (ι_c₀_orderOf Fr) hbc hdisj hC₁ hC₂ hC₃ hO₁ hO₂ hO₃ hR₂2 hbR₂ hcR₂
  have hR₂J : ∀ s ∈ R₂, s ∈ J := fun s hs => by
    obtain ⟨m, hm⟩ := hR₂2 ⟨s, hs⟩
    exact cen_two_mem_J h (Subgroup.mem_centralizer_singleton_iff.mpr (hcen s hs))
      (by simpa using congrArg Subtype.val hm)
  have hsplit : ∀ s ∈ R₂, ∃ a ∈ Asub S A₁, ∃ s' ∈ Jp S J₁, s = a * s' := by
    intro s hs
    obtain ⟨σ, rfl⟩ := S.exists_ι (hR₂J s hs)
    have hsN : S.ι σ ∈ Nor (Asub S A₁) := hRΓ (hR₂R hs)
    have hσ : ∀ u ∈ A₁, σ * u * σ⁻¹ ∈ A₁ := by
      intro u hu
      obtain ⟨u', hu', hue⟩ := conj_mem_Asub hsN (ι_mem_Asub hu)
      have : u' = σ * u * σ⁻¹ := S.ι_injective (by rw [hue, map_mul, map_mul, map_inv])
      rwa [← this]
    obtain ⟨a₁, ha₁, s₁, hs₁, he⟩ := Fr.nor σ hσ
    exact ⟨S.ι a₁, ι_mem_Asub ha₁, S.ι s₁, ⟨s₁, hs₁, rfl⟩, by rw [he, map_mul]⟩
  have hR₂N : R₂ ≤ Nor (Asub S A₁) := fun x hx => hRΓ (hR₂R hx)
  have hT : IsPGroup 2 (R₂ ⊔ Asub S A₁ : Subgroup H) :=
    IsPGroup.to_sup_of_normal_right' hR₂2 (isPGroup_Asub Fr) hR₂N
  have hP : (R₂ ⊔ Asub S A₁) ⊓ Jp S J₁ = ⊥ := by
    refine Jp_two_trivial Fr inf_le_right (hT.to_le inf_le_left) ?_
    intro x hx
    refine ⟨?_, (Jp S J₁).mul_mem ((Jp S J₁).mul_mem (ι_c₀_mem_Jp Fr) hx.2)
      ((Jp S J₁).inv_mem (ι_c₀_mem_Jp Fr))⟩
    have hcT : c ∈ Nor (R₂ ⊔ Asub S A₁) :=
      Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hcR₂, Jp_le_Nor Fr (ι_c₀_mem_Jp Fr)⟩
    exact (Subgroup.mem_normalizer_iff.mp hcT x).mp hx.1
  have hR₂A : R₂ ≤ Asub S A₁ := by
    intro s hs
    obtain ⟨a, ha, s', hs', rfl⟩ := hsplit s hs
    have hs'T : s' ∈ (R₂ ⊔ Asub S A₁) ⊓ Jp S J₁ := by
      refine ⟨?_, hs'⟩
      have : s' = a⁻¹ * (a * s') := by group
      rw [this]
      exact (R₂ ⊔ Asub S A₁).mul_mem ((R₂ ⊔ Asub S A₁).inv_mem (Subgroup.mem_sup_right ha))
        (Subgroup.mem_sup_left hs)
    rw [hP, Subgroup.mem_bot] at hs'T
    rw [hs'T, mul_one]
    exact ha
  have hR₂Z : R₂ ≤ Zsub S A₁ := hR₂A.trans Asub_le_Zsub
  have hdvd : (Zsub S A₁).relIndex R ∣ R₂.relIndex R := Subgroup.relIndex_dvd_of_le_left R hR₂Z
  have hodd : ¬ 2 ∣ (Zsub S A₁).relIndex R := fun h2 => hR₂idx (h2.trans hdvd)
  haveI hZnorm : ((Zsub S A₁).subgroupOf R).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := Zsub_norm (hRΓ g.2) hn
    simpa using this⟩
  have hquot : IsPGroup 2 (↥R ⧸ (Zsub S A₁).subgroupOf R) := by
    intro x
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := hR2 r r.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    show ((r ^ 2 ^ k : ↥R) : H) ∈ Zsub S A₁
    simpa using hk
  obtain ⟨n, hn⟩ := hquot.exists_card_eq
  have hrel : (Zsub S A₁).relIndex R = 2 ^ n := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, hn]
  have hn0 : n = 0 := by
    by_contra hne
    exact hodd (hrel ▸ dvd_pow_self 2 hne)
  rw [hn0, pow_zero] at hrel
  exact Subgroup.relIndex_eq_one.mp hrel

theorem qdata (Fr : Frame A₁ c₀ J₁) (hcop : Nat.Coprime 3 (Nat.card (O1 S A₁)))
    (hC₁ : CtlEq b (S.ι c₀)) (hC₂ : CtlEq b (b * S.ι c₀)) (hC₃ : CtlEq b (b * (S.ι c₀)⁻¹))
    (hO₁ : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers (S.ι c₀))))))
    (hO₂ : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers (b * S.ι c₀))))))
    (hO₃ : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers (b * (S.ι c₀)⁻¹)))))) :
    QData (Nor (Asub S A₁)) (Zsub S A₁) b t (S.ι c₀) (Jp S J₁) where
  Z_le := Zsub_le_Nor Fr
  Z_norm := fun _ hg _ hz => Zsub_norm hg hz
  b_mem := b_mem_Nor Fr
  t_mem := C1_le_Nor t_mem_C1
  c_mem := Jp_le_Nor Fr (ι_c₀_mem_Jp Fr)
  J'_le := fun _ hx => Jp_le_Nor Fr hx
  c_mem_J := ι_c₀_mem_Jp Fr
  b3 := by
    rw [← S.hyp.ord_b]
    exact pow_orderOf_eq_one b
  b_nmem := not_mem_of_orderOf_three (Zsub_cop Fr hcop) S.hyp.ord_b
  t2 := S.hyp.t_sq
  t_nmem := t_not_mem_Zsub Fr
  tb := S.hyp.inv_b
  c3 := ι_c₀_pow_three Fr
  c_nmem := not_mem_of_orderOf_three (Zsub_cop Fr hcop) (ι_c₀_orderOf Fr)
  J'_iso := Jp_iso Fr
  J'_inf_Z := Jp_inf_Zsub Fr
  J'_comm_b := fun j hj => by
    obtain ⟨s, -, rfl⟩ := hj
    exact S.ι_comm_b s
  J'_comm_t := fun j hj => by
    obtain ⟨s, -, rfl⟩ := hj
    exact S.ι_comm_t s
  N_J := fun _ hg _ hj => q_N_J Fr hcop hg hj
  struct_b := q_struct_b Fr hcop
  struct_c := q_struct_c Fr hcop hC₁
  no2 := fun _ hRΓ hZR hR2 hb hc => q_no2 Fr hcop hC₁ hC₂ hC₃ hO₁ hO₂ hO₃ hRΓ hZR hR2 hb hc
  weak := fun _ _ hh => weak_rel S.hyp
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers b)) (by simpa using hh 1)

end Fields

end R38K

end CFSG.RankThree.PartTwo.Sec21.FF81
