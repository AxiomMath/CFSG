module

public import CFSG.Walter.W67.Section5.Prop56GL

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Frame5

variable {s : Std G} (f5 : Frame5 s)

theorem P₁_ne_bot : f5.P₁ ≠ ⊥ := by
  intro h
  have := f5.card_P₁
  rw [h, Subgroup.card_bot] at this
  have := s.three_lt_q
  omega

theorem isPGroup_P₁ (hp : s.p = 3) : IsPGroup 3 f5.P₁ :=
  IsPGroup.of_card (n := s.f) (by rw [f5.card_P₁, Hyp.q, hp])

theorem isElementaryAbelian_P₁ (hp : s.p = 3) : IsElementaryAbelian 3 f5.P₁ :=
  { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (f5.P₁_comm x.1 x.2 y.1 y.2)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by simpa [hp] using f5.P₁_pow x.1 x.2) }

theorem B_comm : ∀ a ∈ f5.B, ∀ b ∈ f5.B, a * b = b * a := by
  have := f5.B_cyclic
  intro a ha b hb
  exact congrArg Subtype.val ((IsCyclic.commGroup (α := f5.B)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem J_mem_centralizer_P₁ : s.J ∈ Subgroup.centralizer (f5.P₁ : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact s.commute_J (s.K_le_H (f5.P₁_le hy))

theorem B_le_normalizer_P₁ : f5.B ≤ Subgroup.normalizer (f5.P₁ : Set G) :=
  fun _ hb => f5.B_le_normalizer (Subgroup.mem_sup_left hb)

theorem E_le_normalizer_P₁ : s.fr.E ≤ Subgroup.normalizer (f5.P₁ : Set G) :=
  fun _ he => f5.B_le_normalizer (Subgroup.mem_sup_right he)

theorem JBE_le_normalizer_P₁ : f5.JBE ≤ Subgroup.normalizer (f5.P₁ : Set G) :=
  sup_le (sup_le (Subgroup.zpowers_le.mpr
    (Subgroup.centralizer_le_normalizer _ f5.J_mem_centralizer_P₁))
    f5.B_le_normalizer_P₁) f5.E_le_normalizer_P₁

theorem JBE_le_H : f5.JBE ≤ s.H :=
  sup_le (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    (f5.B_le.trans s.K_le_H)) s.fr.E_le_H

theorem irred_P₁ {V : Subgroup G} (hV : V ≤ f5.P₁)
    (hVB : ∀ b ∈ f5.B, ∀ v ∈ V, b * v * b⁻¹ ∈ V) : V = ⊥ ∨ V = f5.P₁ := by
  obtain ⟨g, hP₁g, hBg⟩ := f5.exists_std
  rcases f5.irred (h := g) hBg (V := V) (hV.trans hP₁g.le) hVB with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans hP₁g.symm)

theorem irred_JBE : ∀ Q : Subgroup G, Q ≤ f5.P₁ →
    f5.JBE ≤ Subgroup.normalizer (Q : Set G) → Q = ⊥ ∨ Q = f5.P₁ := fun _ hQ hN =>
  f5.irred_P₁ hQ fun _ hb v hv => (Subgroup.mem_normalizer_iff.mp
    (hN (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))) v).mp hv

theorem fpf_P₁ : ∀ b ∈ f5.B, b ≠ 1 → ∀ y ∈ f5.P₁, b * y = y * b → y = 1 := by
  intro b hb hb1 y hy hby
  have : y ∈ f5.P₁ ⊓ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hby.symm⟩
  rwa [f5.fixedPointFree b hb hb1, Subgroup.mem_bot] at this

theorem B_inf_centralizer_P₁ : f5.B ⊓ Subgroup.centralizer (f5.P₁ : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro b hb
  obtain ⟨hbB, hbC⟩ := Subgroup.mem_inf.mp hb
  rw [Subgroup.mem_bot]
  by_contra hb1
  obtain ⟨y, hy, hy1⟩ := (Subgroup.bot_or_exists_ne_one f5.P₁).resolve_left f5.P₁_ne_bot
  exact hy1 (f5.fpf_P₁ b hbB hb1 y hy (Subgroup.mem_centralizer_iff.mp hbC y hy).symm)

theorem mem_P₁_of_odd
    (h26i : S_lemma_2_6_i) {c : G} (hcH : c ∈ s.H)
    (hcC : c ∈ Subgroup.centralizer (f5.P₁ : Set G)) (hodd : Odd (orderOf c)) : c ∈ f5.P₁ := by
  have hcKE := s.fr.mem_KE_of_odd hcH hodd
  have hBN := f5.B_le_normalizer_P₁
  have hEN : s.fr.E ≤ Subgroup.normalizer ((f5.P₁ ⊔ f5.B : Subgroup G) : Set G) :=
    fun e he => Sec52.mem_normalizer_sup (f5.E_le_normalizer_P₁ he) (f5.E_le_normalizer_B he)
  have hk : c ∈ Subgroup.normalizer (f5.P₁ : Set G) ⊓ (s.K ⊔ s.fr.E) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.centralizer_le_normalizer _ hcC, hcKE⟩
  rw [f5.normalizer_eq] at hk
  obtain ⟨y, hy, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hEN).mp hk
  obtain ⟨u, hu, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hBN).mp hy
  have huC : u ∈ Subgroup.centralizer (f5.P₁ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun z hz => f5.P₁_comm z hz _ hu
  have hbeC : b * e ∈ Subgroup.centralizer (f5.P₁ : Set G) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ huC) hcC
    rwa [show u⁻¹ * (u * b * e) = b * e by group] at this
  have hbeB : ∀ b' ∈ f5.B, b * e * b' = b' * (b * e) := by
    intro b' hb'
    have hbeN : b * e ∈ Subgroup.normalizer (f5.B : Set G) :=
      Subgroup.mul_mem _ (Subgroup.le_normalizer hb) (f5.E_le_normalizer_B he)
    have h1 : b * e * b' * (b * e)⁻¹ * b'⁻¹ ∈ f5.B :=
      f5.B.mul_mem ((Subgroup.mem_normalizer_iff.mp hbeN b').mp hb') (f5.B.inv_mem hb')
    have h2 : b * e * b' * (b * e)⁻¹ * b'⁻¹ ∈ Subgroup.centralizer (f5.P₁ : Set G) := by
      have h3 : b' * (b * e)⁻¹ * b'⁻¹ ∈ Subgroup.centralizer (f5.P₁ : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (Sec54.mem_normalizer_centralizer (hBN hb'))
          (b * e)⁻¹).mp (Subgroup.inv_mem _ hbeC)
      rw [show b * e * b' * (b * e)⁻¹ * b'⁻¹ = (b * e) * (b' * (b * e)⁻¹ * b'⁻¹) by group]
      exact Subgroup.mul_mem _ hbeC h3
    have h4 : b * e * b' * (b * e)⁻¹ * b'⁻¹ ∈ f5.B ⊓ Subgroup.centralizer (f5.P₁ : Set G) :=
      Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [f5.B_inf_centralizer_P₁, Subgroup.mem_bot] at h4
    calc b * e * b' = (b * e * b' * (b * e)⁻¹ * b'⁻¹) * (b' * (b * e)) := by group
      _ = b' * (b * e) := by rw [h4, one_mul]
  have he1 : e = 1 := by
    by_contra he1
    obtain ⟨b', hb', hne⟩ := f5.exists_not_comm_B h26i he he1
    apply hne
    calc e * b' = b⁻¹ * (b * e * b') := by group
      _ = b⁻¹ * (b' * (b * e)) := by rw [hbeB b' hb']
      _ = (b⁻¹ * b') * b * e := by group
      _ = (b' * b⁻¹) * b * e := by rw [f5.B_comm _ (f5.B.inv_mem hb) _ hb']
      _ = b' * e := by group
  subst he1
  have hb1 : b = 1 := by
    rw [mul_one] at hbeC
    have : b ∈ f5.B ⊓ Subgroup.centralizer (f5.P₁ : Set G) := Subgroup.mem_inf.mpr ⟨hb, hbeC⟩
    rwa [f5.B_inf_centralizer_P₁, Subgroup.mem_bot] at this
  rw [hb1, mul_one, mul_one]
  exact hu

theorem card_two_le :
    ∀ W : Subgroup G, W ≤ Subgroup.centralizer (f5.P₁ : Set G) →
    IsPGroup 2 W → Nat.card W ≤ 2 := by
  have hJC := f5.J_mem_centralizer_P₁
  apply Sec54.card_le_two hJC s.orderOf_J
  intro W hWC hJW hW w hw
  have hWab := s.toHyp.isMulCommutative_of_isPGroup hW
  have hwJc : Commute s.J w :=
    congrArg Subtype.val (hWab.is_comm.comm ⟨s.J, hJW⟩ ⟨w, hw⟩)
  have hww : w * w = 1 := s.fr.mul_self_of_isPGroup (hW.to_le (Subgroup.zpowers_le.mpr hw))
  have hwC : w ∈ Subgroup.centralizer (f5.P₁ : Set G) := hWC hw
  have hwH : w ∈ s.H := Subgroup.mem_centralizer_singleton_iff.mpr hwJc.eq.symm
  obtain ⟨j, hj, m, hm, rfl⟩ := s.fr.exists_decomp_H_JM hwH
  have hjc : ∀ y ∈ s.K ⊔ s.fr.E, j * y = y * j := fun y hy => s.fr.commute_of_mem_KE hj hy
  have hjj : j * j = 1 := by
    rcases eq_one_or_eq_of_mem_zpowers s.orderOf_J hj with rfl | rfl
    · exact mul_one 1
    · exact s.J_mul_J
  have hmm : m * m = 1 := by
    calc m * m = (j * j)⁻¹ * (j * (j * m) * m) := by group
      _ = (j * j)⁻¹ * (j * (m * j) * m) := by rw [hjc m hm]
      _ = (j * j)⁻¹ * ((j * m) * (j * m)) := by group
      _ = 1 := by rw [hww, hjj]; group
  have hmK := s.fr.mem_K_of_mem_KE_of_mul_self hm hmm
  have hmC : m ∈ Subgroup.centralizer (f5.P₁ : Set G) := by
    have h1 : m = j⁻¹ * (j * m) := by group
    rw [h1]
    exact mul_mem (inv_mem (Subgroup.zpowers_le.mpr hJC hj)) hwC
  have hmP := f5.K_inf_centralizer_le hmK hmC
  have hm1 : m = 1 := by
    have h2 : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hmm])
    have hq : Odd (Nat.card f5.P₁) := by
      rw [f5.card_P₁, Hyp.q]
      exact s.odd_p.pow
    have h3 : orderOf m ∣ Nat.card f5.P₁ := Subgroup.orderOf_dvd_natCard _ hmP
    have h4 : Odd (orderOf m) := Odd.of_dvd_nat hq h3
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at h4
      exact absurd h4 (by decide)
  rw [hm1, mul_one]
  exact hj

theorem exists_R
    (h26i : S_lemma_2_6_i) (hp : s.p = 3) :
    ∃ R : Subgroup G, IsPGroup 3 R ∧ R ≤ Subgroup.centralizer (f5.P₁ : Set G) ∧ f5.P₁ ≤ R ∧
      s.H ⊓ Subgroup.normalizer (f5.P₁ : Set G) ≤ Subgroup.normalizer (R : Set G) ∧
      ∀ Q : Subgroup G, IsPGroup 3 Q → Q ≤ Subgroup.centralizer (f5.P₁ : Set G) →
        Nat.card Q ≤ Nat.card R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (f5.P₁ : Set G) with hCdef
  have hJC := f5.J_mem_centralizer_P₁
  obtain ⟨D, hDC, hDodd, -, hDodd'⟩ := Sec53.exists_index_two hJC s.orderOf_J f5.card_two_le
  have hDN : ∀ g ∈ Subgroup.normalizer (C : Set G), g ∈ Subgroup.normalizer (D : Set G) := by
    intro g hg
    apply Sec53.mem_normalizer_of_conj_le
    intro d hd
    apply hDodd' _ ((Subgroup.mem_normalizer_iff.mp hg d).mp (hDC hd))
    rw [orderOf_conj_mul]
    exact Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard D hd)
  have hodd3 : ∀ Q₀ : Subgroup G, IsPGroup 3 Q₀ → ∀ y ∈ Q₀, Odd (orderOf y) := by
    intro Q₀ hQ₀ y hy
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ₀
    have h1 : orderOf y ∣ 3 ^ k := hk ▸ Subgroup.orderOf_dvd_natCard Q₀ hy
    exact Odd.of_dvd_nat (Odd.pow (by decide)) h1
  set V := Subgroup.zpowers s.J with hVdef
  have hVD : V ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.zpowers_le.mpr (hDN _ (Subgroup.le_normalizer hJC))
  have hV2 : IsPGroup 2 V :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, s.orderOf_J, pow_one])
  have hD2 : ¬ 2 ∣ Nat.card D := fun h2 => (Nat.not_even_iff_odd.mpr hDodd)
    (even_iff_two_dvd.mpr h2)
  let := JT.conjAct V D hVD
  obtain ⟨Q, hQinv⟩ := DisconnectedInvolutionGraph.Helpers.coprime_pgroup_exists_invariant_sylow
    (A := V) 2 3 hV2 hD2
  set R := (Q : Subgroup D).map D.subtype with hRdef
  have hRD : R ≤ D := Subgroup.map_subtype_le _
  have hR3 : IsPGroup 3 R := Q.isPGroup'.map _
  have hRcard : Nat.card R = 3 ^ (Nat.card D).factorization 3 := by
    rw [hRdef, Subgroup.card_map_of_injective D.subtype_injective, Sylow.card_eq_multiplicity]
  have hJR : s.J ∈ Subgroup.normalizer (R : Set G) := by
    apply Sec53.mem_normalizer_of_conj_le
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨_, hQinv ⟨s.J, Subgroup.mem_zpowers _⟩ y hy, rfl⟩
  have huniq : ∀ R' : Subgroup G, R' ≤ D → Nat.card R' = Nat.card R →
      s.J ∈ Subgroup.normalizer (R' : Set G) → R' = R := by
    intro R' hR'D hR'card hJR'
    have hcard' : Nat.card (R'.subgroupOf D) = 3 ^ (Nat.card D).factorization 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR'D).toEquiv, hR'card, hRcard]
    let Q' : Sylow 3 D := Sylow.ofCard (R'.subgroupOf D) hcard'
    have hQ'inv : ∀ v : V, ∀ x ∈ (Q' : Subgroup D), v • x ∈ (Q' : Subgroup D) := by
      intro v x hx
      have hvN : (v : G) ∈ Subgroup.normalizer (R' : Set G) := Subgroup.zpowers_le.mpr hJR' v.2
      exact (Subgroup.mem_normalizer_iff.mp hvN x).mp hx
    obtain ⟨c, hcfix, hc⟩ :=
      SolvableHall.coprime_invariant_sylow_conjugacy hV2 hD2 Q Q' hQinv hQ'inv
    have hcJ : (c : G) ∈ s.H := by
      have h1 := congrArg Subtype.val
        ((FixedPoints.mem_subgroup V D c).mp hcfix ⟨s.J, Subgroup.mem_zpowers _⟩)
      change s.J * (c : G) * s.J⁻¹ = c at h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (c : G) * s.J = s.J * (c : G) * s.J⁻¹ * s.J := by rw [h1]
        _ = s.J * c := by group
    have hcP : (c : G) ∈ f5.P₁ := f5.mem_P₁_of_odd h26i hcJ (hDC c.2)
      (Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard D c.2))
    have hid : (MulAut.conj c⁻¹).toMonoidHom = MonoidHom.id D := by
      refine MonoidHom.ext fun z => Subtype.ext ?_
      have hcz : (c : G) * z = z * c := Subgroup.mem_centralizer_iff.mp (hDC z.2) c hcP
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply,
        Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      rw [mul_assoc, ← hcz, inv_mul_cancel_left]
    rw [hid, Subgroup.map_id] at hc
    have h1 : R'.subgroupOf D = (Q : Subgroup D) := by
      rw [hc]
      exact (Sylow.coe_ofCard _ hcard').symm
    calc R' = (R'.subgroupOf D).map D.subtype := by
          rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hR'D]
      _ = R := by rw [h1]
  refine ⟨R, hR3, hRD.trans hDC, ?_, ?_, ?_⟩
  ·
    have hP₁D : f5.P₁ ≤ D := fun u hu => hDodd' u
      (Subgroup.mem_centralizer_iff.mpr fun z hz => f5.P₁_comm z hz u hu)
      (hodd3 _ (f5.isPGroup_P₁ hp) u hu)
    have hn : (f5.P₁.subgroupOf D).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hgn : (g : G) * n = n * g :=
        (Subgroup.mem_centralizer_iff.mp (hDC g.2) n hn).symm
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hgn, mul_inv_cancel_right]
      exact hn⟩
    have h3 : IsPGroup 3 (f5.P₁.subgroupOf D) :=
      (f5.isPGroup_P₁ hp).comap_of_injective D.subtype D.subtype_injective
    have hle := h3.le_sylow_of_normal Q
    intro u hu
    exact ⟨⟨u, hP₁D hu⟩, hle (Subgroup.mem_subgroupOf.mpr hu), rfl⟩
  ·
    intro g hg
    obtain ⟨hgH, hgN⟩ := Subgroup.mem_inf.mp hg
    have hgD := hDN g (Sec54.mem_normalizer_centralizer hgN)
    set R' := R.map (MulAut.conj g).toMonoidHom with hR'def
    have hR'D : R' ≤ D := by
      rintro _ ⟨r, hr, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hgD r).mp (hRD hr)
    have hR'card : Nat.card R' = Nat.card R :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hgJ : g * s.J = s.J * g := s.commute_J hgH
    have hJR' : s.J ∈ Subgroup.normalizer (R' : Set G) := by
      apply Sec53.mem_normalizer_of_conj_le
      rintro _ ⟨r, hr, rfl⟩
      refine ⟨s.J * r * s.J⁻¹, (Subgroup.mem_normalizer_iff.mp hJR r).mp hr, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hJg : s.J * g⁻¹ = g⁻¹ * s.J := by
        calc s.J * g⁻¹ = g⁻¹ * (g * s.J) * g⁻¹ := by group
          _ = g⁻¹ * (s.J * g) * g⁻¹ := by rw [hgJ]
          _ = g⁻¹ * s.J := by group
      calc g * (s.J * r * s.J⁻¹) * g⁻¹ = (g * s.J) * r * (s.J⁻¹ * g⁻¹) := by group
        _ = (s.J * g) * r * (g⁻¹ * s.J⁻¹) := by
          rw [hgJ, show s.J⁻¹ * g⁻¹ = (g * s.J)⁻¹ by group, hgJ,
            show (s.J * g)⁻¹ = g⁻¹ * s.J⁻¹ by group]
        _ = s.J * (g * r * g⁻¹) * s.J⁻¹ := by group
    have hR'R := huniq R' hR'D hR'card hJR'
    apply Sec53.mem_normalizer_of_conj_le
    intro r hr
    have : g * r * g⁻¹ ∈ R' := ⟨r, hr, rfl⟩
    rwa [hR'R] at this
  ·
    intro Q₀ hQ₀ hQ₀C
    have hQ₀D : Q₀ ≤ D := fun y hy => hDodd' y (hQ₀C hy) (hodd3 Q₀ hQ₀ y hy)
    have hQ₀' : IsPGroup 3 (Q₀.subgroupOf D) :=
      hQ₀.comap_of_injective D.subtype D.subtype_injective
    obtain ⟨S, hS⟩ := hQ₀'.exists_le_sylow
    calc Nat.card Q₀ = Nat.card (Q₀.subgroupOf D) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₀D).toEquiv).symm
      _ ≤ Nat.card S := Subgroup.card_le_of_le hS
      _ = Nat.card R := by rw [Sylow.card_eq_multiplicity, hRcard]

theorem three_mul_le_three_pow : ∀ a : ℕ, 3 * a ≤ 3 ^ a
  | 0 => by norm_num
  | a + 1 => by
    have h := three_mul_le_three_pow a
    have h1 : 1 ≤ 3 ^ a := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_succ]
    omega

theorem card_P₁_inf_centralizer_le (h26i : S_lemma_2_6_i) (hp : s.p = 3) {Y : Subgroup G}
    (hYE : Y ≤ s.fr.E) (hY : Y ≠ ⊥) :
    Nat.card (f5.P₁ ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) ≤
      3 ^ (s.f / Nat.card Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have heX : s.eX Y = Nat.card Y := by
    rw [Hyp.eX, s.F_eq_bot, sup_bot_eq, Subgroup.card_bot, Nat.div_one]
  obtain ⟨hediv, ⟨eKY⟩, -⟩ := h26i G s.toHyp s.fr hYE hY
  rw [heX] at hediv
  have hmpos : 0 < s.f / s.eX Y := by
    rw [heX]
    exact Nat.div_pos (Nat.le_of_dvd s.f_pos hediv) Nat.card_pos
  have hle : f5.P₁ ⊓ Subgroup.centralizer (Y : Set G) ≤ s.KX Y := fun y hy =>
    Subgroup.mem_inf.mpr ⟨f5.P₁_le (Subgroup.mem_inf.mp hy).1, (Subgroup.mem_inf.mp hy).2⟩
  have hdvd := Subgroup.card_dvd_of_le hle
  have hFcard : Nat.card (GaloisField s.p (s.f / s.eX Y)) = s.p ^ (s.f / s.eX Y) :=
    GaloisField.card _ _ hmpos.ne'
  rw [Nat.card_congr eKY.toEquiv, psl2_card_formula _ ⟨s.p, s.f / s.eX Y, Fact.out, s.odd_p,
    hmpos, hFcard⟩, hFcard] at hdvd
  rw [heX] at hdvd hmpos
  rw [hp] at hdvd
  set m := s.f / Nat.card Y
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((f5.isPGroup_P₁ hp).to_le
    (inf_le_left : f5.P₁ ⊓ Subgroup.centralizer (Y : Set G) ≤ f5.P₁))
  rw [hk] at hdvd ⊢
  have hev := Borel5.even_mul_sq_sub_one (Odd.pow (by decide : Odd 3) : Odd (3 ^ m))
  have h1 : 3 ^ k ∣ 3 ^ m * ((3 ^ m) ^ 2 - 1) :=
    hdvd.trans (Nat.div_dvd_of_dvd (even_iff_two_dvd.mp hev))
  have hcop : Nat.Coprime (3 ^ k) ((3 ^ m) ^ 2 - 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h
    have h3 : 3 ∣ (3 ^ m) ^ 2 := dvd_pow (dvd_pow_self 3 hmpos.ne') two_ne_zero
    have := Nat.dvd_sub h3 h
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by positivity))] at this
    norm_num at this
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right h1)

theorem three_mul_le_f (h26i : S_lemma_2_6_i) {P₀ : Subgroup G} (hP₀E : P₀ ≤ s.fr.E)
    {k : ℕ} (hk : Nat.card P₀ = 3 ^ k) : 3 * k ≤ s.f := by
  have heX : s.eX s.fr.E = Nat.card s.fr.E := by
    rw [Hyp.eX, s.F_eq_bot, sup_bot_eq, Subgroup.card_bot, Nat.div_one]
  obtain ⟨hediv, -, -⟩ := h26i G s.toHyp s.fr le_rfl s.E_ne_bot
  rw [heX] at hediv
  have h1 : 3 ^ k ∣ s.f := hk ▸ (Subgroup.card_dvd_of_le hP₀E).trans hediv
  exact (three_mul_le_three_pow k).trans (Nat.le_of_dvd s.f_pos h1)

theorem le_P₁_of_comm (h26i : S_lemma_2_6_i) (hp : s.p = 3) {P₀ : Subgroup G}
    (hP₀E : P₀ ≤ s.fr.E) (hP₀ : IsPGroup 3 P₀) {A : Subgroup G}
    (hA : A ≤ f5.P₁ ⊔ P₀) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAcard : Nat.card f5.P₁ ≤ Nat.card A) : A ≤ f5.P₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hnot
  obtain ⟨a₀, ha₀A, ha₀P⟩ := Set.not_subset.mp hnot
  have hP₀N : P₀ ≤ Subgroup.normalizer (f5.P₁ : Set G) := hP₀E.trans f5.E_le_normalizer_P₁
  obtain ⟨u, hu, y, hy, rfl⟩ := (mem_sup_iff_of_le_normalizer hP₀N).mp (hA ha₀A)
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact ha₀P (by rw [mul_one]; exact hu)
  set Y := Subgroup.zpowers y with hYdef
  have hYE : Y ≤ s.fr.E := Subgroup.zpowers_le.mpr (hP₀E hy)
  have hY1 : Y ≠ ⊥ := by
    intro h
    apply hy1
    have : y ∈ Y := Subgroup.mem_zpowers y
    rwa [h, Subgroup.mem_bot] at this
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP₀
  have hY3 : 3 ≤ Nat.card Y := by
    rw [Nat.card_zpowers]
    have hdvd : orderOf y ∣ 3 ^ k := hk ▸ Subgroup.orderOf_dvd_natCard P₀ hy
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hj]
    rcases j with _ | j
    · exact absurd (orderOf_eq_one_iff.mp (by rw [hj, pow_zero])) hy1
    · exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_succ
        (Nat.zero_le j)))
  have hle : A ⊓ f5.P₁ ≤ f5.P₁ ⊓ Subgroup.centralizer (Y : Set G) := by
    intro w hw
    obtain ⟨hwA, hwP⟩ := Subgroup.mem_inf.mp hw
    refine Subgroup.mem_inf.mpr ⟨hwP, ?_⟩
    rw [hYdef, Sec52.centralizer_zpowers_eq, Subgroup.mem_centralizer_singleton_iff]
    have h1 : (u * y) * w = w * (u * y) := hAc _ ha₀A w hwA
    have h2 : u * w = w * u := f5.P₁_comm u hu w hwP
    calc w * y = u⁻¹ * (u * w) * y := by group
      _ = u⁻¹ * (w * u) * y := by rw [h2]
      _ = u⁻¹ * (w * (u * y)) := by group
      _ = u⁻¹ * (u * y * w) := by rw [← h1]
      _ = y * w := by group
  have h1 := Subgroup.card_le_of_le hle
  have h2 := f5.card_P₁_inf_centralizer_le h26i hp hYE hY1
  have hAN : A ≤ Subgroup.normalizer (f5.P₁ : Set G) :=
    hA.trans (sup_le Subgroup.le_normalizer hP₀N)
  have h3 := Sec52.card_sup_mul_card_inf hAN
  have h4 := Sec52.card_sup_mul_card_inf hP₀N
  have h5 : Nat.card (A ⊔ f5.P₁ : Subgroup G) ≤ Nat.card (P₀ ⊔ f5.P₁ : Subgroup G) :=
    Subgroup.card_le_of_le (sup_le (hA.trans (le_of_eq (sup_comm _ _))) le_sup_right)
  have h6 : 0 < Nat.card (f5.P₁ ⊓ P₀ : Subgroup G) := Nat.card_pos
  have h7 : 0 < Nat.card f5.P₁ := Nat.card_pos
  have hcomm : f5.P₁ ⊓ A = A ⊓ f5.P₁ := inf_comm _ _
  rw [hcomm] at h3
  have h8 : Nat.card A ≤ Nat.card P₀ * Nat.card (A ⊓ f5.P₁ : Subgroup G) := by
    have h9 : Nat.card f5.P₁ * Nat.card A ≤
        Nat.card f5.P₁ * (Nat.card P₀ * Nat.card (A ⊓ f5.P₁ : Subgroup G)) := by
      rw [← h3]
      calc Nat.card (A ⊔ f5.P₁ : Subgroup G) * Nat.card (A ⊓ f5.P₁ : Subgroup G)
          ≤ Nat.card (P₀ ⊔ f5.P₁ : Subgroup G) * Nat.card (A ⊓ f5.P₁ : Subgroup G) :=
            Nat.mul_le_mul_right _ h5
        _ ≤ Nat.card (P₀ ⊔ f5.P₁ : Subgroup G) * Nat.card (f5.P₁ ⊓ P₀ : Subgroup G) *
            Nat.card (A ⊓ f5.P₁ : Subgroup G) :=
            Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ h6)
        _ = Nat.card f5.P₁ * (Nat.card P₀ * Nat.card (A ⊓ f5.P₁ : Subgroup G)) := by
            rw [h4, mul_assoc]
    exact Nat.le_of_mul_le_mul_left h9 h7
  rw [hk] at h8
  have hq : Nat.card f5.P₁ = 3 ^ s.f := by rw [f5.card_P₁, Hyp.q, hp]
  have h10 : 3 ^ s.f ≤ 3 ^ (k + s.f / Nat.card Y) := by
    rw [pow_add]
    calc 3 ^ s.f = Nat.card f5.P₁ := hq.symm
      _ ≤ Nat.card A := hAcard
      _ ≤ 3 ^ k * Nat.card (A ⊓ f5.P₁ : Subgroup G) := h8
      _ ≤ 3 ^ k * 3 ^ (s.f / Nat.card Y) := Nat.mul_le_mul_left _ (h1.trans h2)
  have h11 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h10
  have h12 : s.f / Nat.card Y ≤ s.f / 3 := Nat.div_le_div_left hY3 (by norm_num)
  have h13 := three_mul_le_f h26i hP₀E hk
  have h14 := s.f_pos
  omega

theorem three_not_dvd_JB (hp : s.p = 3) :
    ¬ 3 ∣ Nat.card (Subgroup.zpowers s.J ⊔ f5.B : Subgroup G) := by
  have hB3 : ¬ 3 ∣ Nat.card f5.B := by
    intro h3
    have := f5.card_B
    rw [Hyp.q, hp] at this
    have h3' : 3 ∣ 3 ^ s.f := dvd_pow_self 3 s.f_pos.ne'
    have h3'' : 3 ∣ 3 ^ s.f - 1 := this ▸ (Dvd.dvd.mul_left h3 2)
    have := Nat.dvd_sub h3' h3''
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by norm_num))] at this
    norm_num at this
  have hzJ : f5.B ≤ Subgroup.normalizer ((Subgroup.zpowers s.J : Subgroup G) : Set G) := by
    intro b hb
    apply Sec53.mem_normalizer_of_conj_le
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hbJ : Commute b s.J := s.commute_J (s.K_le_H (f5.B_le hb))
    rw [show b * s.J ^ k * b⁻¹ = s.J ^ k by
      rw [(Commute.zpow_right hbJ k).eq, mul_inv_cancel_right]]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  have h1 := Sec52.card_sup_mul_card_inf hzJ
  rw [Nat.card_zpowers, s.orderOf_J, sup_comm] at h1
  intro h3
  have : 3 ∣ 2 * Nat.card f5.B := h3.trans (Dvd.intro _ h1)
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp this with h | h
  · norm_num at h
  · exact hB3 h

theorem card_JBE_dvd :
    Nat.card f5.JBE ∣ Nat.card (Subgroup.zpowers s.J ⊔ f5.B : Subgroup G) * Nat.card s.fr.E := by
  have hEN : s.fr.E ≤ Subgroup.normalizer
      ((Subgroup.zpowers s.J ⊔ f5.B : Subgroup G) : Set G) := by
    intro e he
    have hzJ : e ∈ Subgroup.normalizer ((Subgroup.zpowers s.J : Subgroup G) : Set G) := by
      apply Sec53.mem_normalizer_of_conj_le
      intro z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have heJ : Commute e s.J := s.commute_J (s.fr.E_le_H he)
      rw [show e * s.J ^ k * e⁻¹ = s.J ^ k by
        rw [(Commute.zpow_right heJ k).eq, mul_inv_cancel_right]]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
    exact Sec52.mem_normalizer_sup hzJ (f5.E_le_normalizer_B he)
  have h1 := Sec52.card_sup_mul_card_inf hEN
  rw [sup_comm] at h1
  exact Dvd.intro _ h1

theorem card_le_of_le_normalizer (hp : s.p = 3) {P : Subgroup G}
    (hN : Subgroup.normalizer (P : Set G) = f5.JBE ⊔ Subgroup.centralizer (P : Set G))
    {Q : Subgroup G} (hQ : IsPGroup 3 Q) (hQN : Q ≤ Subgroup.normalizer (P : Set G)) :
    Nat.card Q ≤ 3 ^ (Nat.card s.fr.E).factorization 3 *
      Nat.card (Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) := by
  set C := Subgroup.centralizer (P : Set G) with hCdef
  have hCN' : ∀ g ∈ Subgroup.normalizer (P : Set G), g ∈ Subgroup.normalizer (C : Set G) :=
    fun g hg => Sec54.mem_normalizer_centralizer hg
  have h1 := Sec52.card_sup_mul_card_inf (A := C) (C := Q) (fun g hg => hCN' g (hQN hg))
  have hJBEN : f5.JBE ≤ Subgroup.normalizer (P : Set G) := by rw [hN]; exact le_sup_left
  have h2 := Sec52.card_sup_mul_card_inf (A := C) (C := f5.JBE)
    (fun g hg => hCN' g (hJBEN hg))
  have h3 : Q ⊔ C ≤ f5.JBE ⊔ C := by
    rw [← hN]
    exact sup_le hQN (Subgroup.centralizer_le_normalizer _)
  have h4 := Subgroup.card_dvd_of_le h3
  have hx : Nat.card (C ⊓ Q : Subgroup G) = Nat.card (Q ⊓ C : Subgroup G) := by rw [inf_comm]
  have hdiv : Nat.card Q ∣ Nat.card f5.JBE * Nat.card (Q ⊓ C : Subgroup G) := by
    obtain ⟨t, ht⟩ := h4
    have hc : 0 < Nat.card C := Nat.card_pos
    refine ⟨t * Nat.card (C ⊓ f5.JBE : Subgroup G), ?_⟩
    have : Nat.card C * (Nat.card f5.JBE * Nat.card (Q ⊓ C : Subgroup G)) =
        Nat.card C * (Nat.card Q * (t * Nat.card (C ⊓ f5.JBE : Subgroup G))) := by
      calc Nat.card C * (Nat.card f5.JBE * Nat.card (Q ⊓ C : Subgroup G))
          = (Nat.card C * Nat.card f5.JBE) * Nat.card (Q ⊓ C : Subgroup G) := by ring
        _ = (Nat.card (f5.JBE ⊔ C : Subgroup G) * Nat.card (C ⊓ f5.JBE : Subgroup G)) *
            Nat.card (Q ⊓ C : Subgroup G) := by rw [h2]
        _ = (Nat.card (Q ⊔ C : Subgroup G) * t * Nat.card (C ⊓ f5.JBE : Subgroup G)) *
            Nat.card (Q ⊓ C : Subgroup G) := by rw [ht]
        _ = (Nat.card (Q ⊔ C : Subgroup G) * Nat.card (C ⊓ Q : Subgroup G)) * t *
            Nat.card (C ⊓ f5.JBE : Subgroup G) := by rw [hx]; ring
        _ = (Nat.card C * Nat.card Q) * t * Nat.card (C ⊓ f5.JBE : Subgroup G) := by rw [h1]
        _ = Nat.card C * (Nat.card Q * (t * Nat.card (C ⊓ f5.JBE : Subgroup G))) := by ring
    exact Nat.eq_of_mul_eq_mul_left hc this
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQ
  obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp (hQ.to_le (inf_le_left : Q ⊓ C ≤ Q))
  have hle : i ≤ m := by
    have := Subgroup.card_le_of_le (inf_le_left : Q ⊓ C ≤ Q)
    rw [hm, hi] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  rw [hm, hi] at hdiv ⊢
  have h5 : 3 ^ (m - i) ∣ Nat.card f5.JBE := by
    rw [← Nat.sub_add_cancel hle, pow_add] at hdiv
    exact Nat.dvd_of_mul_dvd_mul_right (pow_pos (by norm_num) i) hdiv
  have h6 : 3 ^ (m - i) ∣ Nat.card s.fr.E := by
    have h7 := h5.trans f5.card_JBE_dvd
    have hcop : Nat.Coprime (3 ^ (m - i))
        (Nat.card (Subgroup.zpowers s.J ⊔ f5.B : Subgroup G)) :=
      Nat.Coprime.pow_left _
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (f5.three_not_dvd_JB hp))
    exact hcop.dvd_of_dvd_mul_left h7
  have h8 : m - i ≤ (Nat.card s.fr.E).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h6
  calc 3 ^ m = 3 ^ (m - i) * 3 ^ i := by rw [← pow_add, Nat.sub_add_cancel hle]
    _ ≤ 3 ^ (Nat.card s.fr.E).factorization 3 * 3 ^ i :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) h8)

open Sec52 in
theorem false_of_card_centralizer
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    (h3 : 3 ∣ Nat.card s.fr.E)
    (hC : ∀ Q : Subgroup G, IsPGroup 3 Q → Q ≤ Subgroup.centralizer (f5.P₁ : Set G) →
      Nat.card Q ≤ Nat.card f5.P₁) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h54 := lemma_5_4_of h22 h26i
  have hN := h54 G s hp f5 f5.P₁ (f5.isElementaryAbelian_P₁ hp) f5.P₁_ne_bot
    f5.JBE_le_normalizer_P₁ f5.irred_JBE
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 s.fr.E) := inferInstance
  set P₀ := (S₀ : Subgroup s.fr.E).map s.fr.E.subtype with hP₀def
  have hP₀E : P₀ ≤ s.fr.E := Subgroup.map_subtype_le _
  have hP₀3 : IsPGroup 3 P₀ := S₀.isPGroup'.map _
  set a := (Nat.card s.fr.E).factorization 3 with ha
  have hP₀card : Nat.card P₀ = 3 ^ a := by
    rw [hP₀def, Subgroup.card_map_of_injective s.fr.E.subtype_injective,
      Sylow.card_eq_multiplicity]
  have hapos : 0 < a := Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' h3
  set Q := f5.P₁ ⊔ P₀ with hQdef
  have hP₀N : P₀ ≤ Subgroup.normalizer (f5.P₁ : Set G) := hP₀E.trans f5.E_le_normalizer_P₁
  have hinf : f5.P₁ ⊓ P₀ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have : y ∈ s.K ⊓ s.fr.E := Subgroup.mem_inf.mpr
      ⟨f5.P₁_le (Subgroup.mem_inf.mp hy).1, hP₀E (Subgroup.mem_inf.mp hy).2⟩
    rwa [s.fr.K_inf_E] at this
  have hQcard : Nat.card Q = Nat.card f5.P₁ * 3 ^ a := by
    rw [hQdef, Sec54.card_sup_eq_mul hP₀N hinf, hP₀card]
  have hQ3 : IsPGroup 3 Q := IsPGroup.of_card (n := s.f + a)
    (by rw [hQcard, f5.card_P₁, Hyp.q, hp, pow_add])
  have hQN : Q ≤ Subgroup.normalizer (f5.P₁ : Set G) := sup_le Subgroup.le_normalizer hP₀N
  have hQmax : ∀ Q' : Subgroup G, IsPGroup 3 Q' → Q ≤ Q' →
      Q' ≤ Subgroup.normalizer (f5.P₁ : Set G) → Q' ≤ Q := by
    intro Q' hQ' hQQ' hQ'N
    have h1 := f5.card_le_of_le_normalizer hp hN hQ' hQ'N
    have h2 := hC _ (hQ'.to_le inf_le_left) inf_le_right
    have hle : Nat.card Q' ≤ Nat.card Q := by
      rw [hQcard]
      calc Nat.card Q' ≤ 3 ^ a * Nat.card (Q' ⊓ Subgroup.centralizer (f5.P₁ : Set G) :
            Subgroup G) := h1
        _ ≤ 3 ^ a * Nat.card f5.P₁ := Nat.mul_le_mul_left _ h2
        _ = Nat.card f5.P₁ * 3 ^ a := mul_comm _ _
    exact (Subgroup.eq_of_le_of_card_ge hQQ' hle).ge
  have hconj : ∀ g : G, f5.P₁.map (MulAut.conj g).toMonoidHom ≤ Q →
      f5.P₁.map (MulAut.conj g).toMonoidHom = f5.P₁ := by
    intro g hg
    have hAc : ∀ a ∈ f5.P₁.map (MulAut.conj g).toMonoidHom,
        ∀ b ∈ f5.P₁.map (MulAut.conj g).toMonoidHom, a * b = b * a := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group, f5.P₁_comm a ha b hb]
      group
    have hcard : Nat.card f5.P₁ ≤ Nat.card (f5.P₁.map (MulAut.conj g).toMonoidHom) :=
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
    have hle := f5.le_P₁_of_comm h26i hp hP₀E hP₀3 hg hAc hcard
    exact Subgroup.eq_of_le_of_card_ge hle hcard
  have hweak : ∀ g : G, (∀ w ∈ f5.P₁, g * w * g⁻¹ ∈ Q) → ∀ w ∈ f5.P₁, g * w * g⁻¹ ∈ f5.P₁ := by
    intro g hg w hw
    have h1 := hconj g (by rintro _ ⟨v, hv, rfl⟩; exact hg v hv)
    have : g * w * g⁻¹ ∈ f5.P₁.map (MulAut.conj g).toMonoidHom := ⟨w, hw, rfl⟩
    rwa [h1] at this
  let P : Sylow 3 G := ⟨Q, hQ3, fun hS hQS =>
    Sec56.eq_of_le_of_weaklyClosed le_sup_left hQN hQmax hweak hS hQS⟩
  have hWC : BenderSuzuki.External.WeaklyClosedIn (P : Subgroup G) f5.P₁ :=
    ⟨le_sup_left, fun g hg => hconj g⁻¹ hg⟩
  have hres := Sec56.hallPResidual_normalizer_eq s.perfect P hWC f5.P₁_comm
  have h3P₀ : 3 ∣ Nat.card P₀ := by
    rw [hP₀card]
    exact dvd_pow_self 3 hapos.ne'
  obtain ⟨⟨x, hxP₀⟩, hox⟩ := exists_prime_orderOf_dvd_card' (G := P₀) 3 h3P₀
  rw [Subgroup.orderOf_mk] at hox
  have hxE : x ∈ s.fr.E := hP₀E hxP₀
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hox
    norm_num at hox
  have hxB := f5.exists_not_comm_B h26i hxE hx1
  apply Frame5.not_mem_hallPResidual h54 hp f5 (f5.isElementaryAbelian_P₁ hp) f5.P₁_ne_bot
    f5.JBE_le_normalizer_P₁ f5.irred_JBE f5.fpf_P₁ hxE hox hxB
  rw [hres]
  exact f5.E_le_normalizer_P₁ hxE

end Frame5

end CFSG.Walter.W67
