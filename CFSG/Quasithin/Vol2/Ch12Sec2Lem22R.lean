module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22O

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem22

variable {G : Type} [Group G] [Finite G]

theorem conj_eq_of_frattini {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hPp : IsPGroup p ↥P) {d : G} (hd : d ∈ Subgroup.normalizer (P : Set G)) {k : ℕ}
    (hdk : ∀ x ∈ P, d ^ 2 ^ k * x * (d ^ 2 ^ k)⁻¹ = x)
    (hdΦ : ∀ x ∈ P, d * x * d⁻¹ * x⁻¹ ∈ (frattini ↥P).map P.subtype) :
    ∀ x ∈ P, d * x * d⁻¹ = x := by
  have : Fact p.Prime := ⟨hp⟩
  have hdP : ∀ x ∈ P, d * x * d⁻¹ ∈ P := fun x hx => (Subgroup.mem_normalizer_iff.mp hd x).mp hx
  have hdP' : ∀ x ∈ P, d⁻¹ * x * d ∈ P := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hd) x).mp hx
    rwa [inv_inv] at this
  let τ : MulAut ↥P :=
    { toFun := fun x => ⟨d * x * d⁻¹, hdP x x.2⟩
      invFun := fun x => ⟨d⁻¹ * x * d, hdP' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        group) }
  have hτ : ∀ x : ↥P, ((τ x : ↥P) : G) = d * x * d⁻¹ := fun _ => rfl
  have hτpow : ∀ j : ℕ, ∀ x : ↥P, (((τ ^ j) x : ↥P) : G) = d ^ j * x * (d ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, hτ, ih, pow_succ']
      group
  have hτk : τ ^ 2 ^ k = 1 := by
    ext x
    rw [hτpow, hdk x x.2, MulAut.one_apply]
  have hcop : Nat.Coprime p (orderOf τ) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hτk)
      (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))
  have hfrat : CFSG.Walter.Huppert.frattiniAut ↥P τ = 1 := by
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [CFSG.Walter.Huppert.frattiniAut_mk, MulAut.one_apply, QuotientGroup.eq]
    obtain ⟨f₀, hf₀, hf₀e⟩ := hdΦ x x.2
    have e : (τ x)⁻¹ * x = (x : ↥P)⁻¹ * f₀⁻¹ * x := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hτ]
      rw [show ((f₀ : ↥P) : G) = d * x * d⁻¹ * (x : G)⁻¹ from hf₀e]
      group
    rw [e]
    have := (inferInstance : (frattini ↥P).Normal).conj_mem _ (Subgroup.inv_mem _ hf₀)
      (x : ↥P)⁻¹
    simpa [mul_assoc] using this
  have hτ1 := CFSG.Walter.Huppert.eq_one_of_frattiniAut_eq_one hPp hcop hfrat
  intro x hx
  have := congrArg (fun σ : MulAut ↥P => ((σ ⟨x, hx⟩ : ↥P) : G)) hτ1
  simpa only [MulAut.one_apply, hτ] using this

namespace Extra3

variable {T L V H P U I : Subgroup G} {h : G}

theorem mem_of_comm (h331 : Stmt3_3_1) (e : Extra3 T L V H P U I h) :
    ∀ t ∈ T, (∀ x ∈ P, t * x = x * t) → t ∈ pCoreOf 2 H := by
  obtain ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, hHPT, -, hhP, hhM, -⟩ := e.pre
  set Q := pCoreOf 2 H with hQ
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  have hP1 : P ≠ ⊥ := fun h0 => hh1 (by rw [h0] at hhP; exact Subgroup.mem_bot.mp hhP)
  have hmin := Lem7.minParabolic h331 e.hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hQT : Q ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hHO : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hconjO : ∀ g ∈ H, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hHO hg) y).mp hy
  set C := T ⊓ Subgroup.centralizer (P : Set G) with hC
  have hCQ : C ≤ Subgroup.normalizer (Q : Set G) := fun c hc => hHO (hTH hc.1)
  set QC := Q ⊔ C with hQCdef
  have hQCmem : ∀ y ∈ QC, ∃ q ∈ Q, ∃ c ∈ C, y = q * c := by
    intro y hy
    rw [hQCdef, sup_comm, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCQ] at hy
    obtain ⟨c, hc, q, hq, hcq⟩ := hy
    refine ⟨c * q * c⁻¹, hconjO c (hTH hc.1) q hq, c, hc, ?_⟩
    rw [← hcq]
    group
  have hQCT : QC ≤ T := sup_le hQT inf_le_left
  have hQCp : IsPGroup 2 ↥QC := hmin.isSylow.2.1.to_le hQCT
  have hnorm : ∀ g : G, (∀ y ∈ QC, g * y * g⁻¹ ∈ QC) → g ∈ Subgroup.normalizer (QC : Set G) :=
    fun g hg => Sec121Swap.mem_normalizer_of_conj_mem hg
  have hPn : P ≤ Subgroup.normalizer (QC : Set G) := by
    intro x hx
    refine hnorm x fun y hy => ?_
    obtain ⟨q, hq, c, hc, rfl⟩ := hQCmem y hy
    have hxc : x * c = c * x := ((Subgroup.mem_centralizer_iff.mp hc.2) x hx)
    have e1 : x * (q * c) * x⁻¹ = (x * q * x⁻¹) * c := by
      calc x * (q * c) * x⁻¹ = (x * q * x⁻¹) * (x * c) * x⁻¹ := by group
        _ = (x * q * x⁻¹) * (c * x) * x⁻¹ := by rw [hxc]
        _ = (x * q * x⁻¹) * c := by group
    rw [e1]
    exact QC.mul_mem (Subgroup.mem_sup_left (hconjO x (hPH hx) q hq)) (Subgroup.mem_sup_right hc)
  have hTn : T ≤ Subgroup.normalizer (QC : Set G) := by
    intro t ht
    refine hnorm t fun y hy => ?_
    obtain ⟨q, hq, c, hc, rfl⟩ := hQCmem y hy
    obtain ⟨q₀, hq₀, hq₀t⟩ := exists_mul_mem_normalizer h331 e.hyp hHs hsol hp hp2 hPp hPH hPi
      hP1 (hTH ht)
    have hnT : q₀ * t ∈ T := T.mul_mem (hQT hq₀) ht
    have hnC : (q₀ * t) * c * (q₀ * t)⁻¹ ∈ C := by
      refine ⟨T.mul_mem (T.mul_mem hnT hc.1) (T.inv_mem hnT), ?_⟩
      show (q₀ * t) * c * (q₀ * t)⁻¹ ∈ Subgroup.centralizer (P : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : (q₀ * t)⁻¹ * x * (q₀ * t) ∈ P := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hq₀t) x).mp hx
        simpa using this
      have hcx := (Subgroup.mem_centralizer_iff.mp hc.2) _ hx'
      calc x * ((q₀ * t) * c * (q₀ * t)⁻¹)
          = (q₀ * t) * (((q₀ * t)⁻¹ * x * (q₀ * t)) * c) * (q₀ * t)⁻¹ := by group
        _ = (q₀ * t) * (c * ((q₀ * t)⁻¹ * x * (q₀ * t))) * (q₀ * t)⁻¹ := by rw [hcx]
        _ = (q₀ * t) * c * (q₀ * t)⁻¹ * x := by group
    have htq : t * q * t⁻¹ ∈ Q := hconjO t (hTH ht) q hq
    have e1 : t * (q * c) * t⁻¹ = (t * q * t⁻¹) * (q₀⁻¹ * ((q₀ * t) * c * (q₀ * t)⁻¹) * q₀) := by
      group
    rw [e1]
    refine QC.mul_mem (Subgroup.mem_sup_left htq) ?_
    set c' := (q₀ * t) * c * (q₀ * t)⁻¹ with hc'
    have hc'H : c' ∈ H := hTH hnC.1
    have e2 : q₀⁻¹ * c' * q₀ = (q₀⁻¹ * (c' * q₀ * c'⁻¹)) * c' := by group
    rw [e2]
    exact QC.mul_mem (Subgroup.mem_sup_left (Q.mul_mem (Q.inv_mem hq₀)
      (hconjO c' hc'H q₀ hq₀))) (Subgroup.mem_sup_right hnC)
  have hQCH : QC ≤ H := hQCT.trans hTH
  have hle : QC ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQCH
    (fun g hg => (sup_le hPn hTn) (hHPT ▸ hg)) hQCp
  intro t ht htP
  exact hle (Subgroup.mem_sup_right ⟨ht, Subgroup.mem_centralizer_iff.mpr fun x hx =>
    (htP x hx).symm⟩)


theorem inv_or_triv (e : Extra3 T L V H P U I h) {c : G}
    (hcP : c ∈ Subgroup.normalizer (P : Set G))
    (hcΦ : ∀ f ∈ (frattini ↥P).map P.subtype, c * f = f * c)
    (hc2 : ∀ x ∈ P, (c * c) * x * (c * c)⁻¹ = x) :
    (∀ x ∈ P, c * x * c⁻¹ * x⁻¹ ∈ (frattini ↥P).map P.subtype) ∨
      (∀ x ∈ P, c * x * c⁻¹ * x ∈ (frattini ↥P).map P.subtype) := by
  obtain ⟨-, -, hp, hp2, hPp, -⟩ := e.pre
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  have hΦP : Φ ≤ P := frattini_map_le P
  have hcP' : ∀ x ∈ P, c * x * c⁻¹ ∈ P := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hcP x).mp hx
  have hZ := e.central
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Φ := fun x hx y hy =>
    commutator_mem_frattini_map hp hPp hx hy
  have hnormΦ : ∀ x ∈ P, ∀ f ∈ Φ, x * f * x⁻¹ ∈ Φ := fun x hx f hf =>
    conj_mem_frattini (Subgroup.le_normalizer hx) hf
  have hsqΦ : ∀ z ∈ P, z * z ∈ Φ → z ∈ Φ := by
    intro z hz hz2
    have hz3 : z ^ 3 = 1 := e.exp z hz
    have e1 : z = (z * z) * (z * z) := by
      calc z = z ^ 3 * z := by rw [hz3, one_mul]
        _ = (z * z) * (z * z) := by rw [pow_three]; group
    rw [e1]
    exact Φ.mul_mem hz2 hz2
  by_contra hno
  push Not at hno
  obtain ⟨⟨y, hy, hy1⟩, ⟨x, hx, hx1⟩⟩ := hno
  have hsxP := hcP' x hx
  have hsyP := hcP' y hy
  set a := x * (c * x * c⁻¹) with ha
  set b := y * (c * y * c⁻¹)⁻¹ with hb
  have haP : a ∈ P := P.mul_mem hx hsxP
  have hbP : b ∈ P := P.mul_mem hy (P.inv_mem hsyP)
  have haΦ : a ∉ Φ := fun h0 => hx1 (by
    have e1 : c * x * c⁻¹ * x = x⁻¹ * a * x := by rw [ha]; group
    rw [e1]
    have h1 := hnormΦ x⁻¹ (P.inv_mem hx) a h0
    simpa using h1)
  have hbΦ : b ∉ Φ := fun h0 => hy1 (by
    have e1 : c * y * c⁻¹ * y⁻¹ = b⁻¹ := by rw [hb]; group
    rw [e1]
    exact Φ.inv_mem h0)
  have hσb : c * b * c⁻¹ = b⁻¹ := by
    have h2 := hc2 y hy
    rw [hb]
    calc c * (y * (c * y * c⁻¹)⁻¹) * c⁻¹ = (c * y * c⁻¹) * ((c * c) * y * (c * c)⁻¹)⁻¹ := by
          group
      _ = (c * y * c⁻¹) * y⁻¹ := by rw [h2]
      _ = (y * (c * y * c⁻¹)⁻¹)⁻¹ := by group
  set f₀ := a⁻¹ * (c * a * c⁻¹) with hf₀
  have hf₀Φ : f₀ ∈ Φ := by
    have h2 := hc2 x hx
    have e1 : c * a * c⁻¹ = (c * x * c⁻¹) * x := by
      rw [ha]
      calc c * (x * (c * x * c⁻¹)) * c⁻¹ = (c * x * c⁻¹) * ((c * c) * x * (c * c)⁻¹) := by
            group
        _ = (c * x * c⁻¹) * x := by rw [h2]
    have e2 : f₀ = (c * x * c⁻¹)⁻¹ * x⁻¹ * (c * x * c⁻¹)⁻¹⁻¹ * x⁻¹⁻¹ := by
      rw [hf₀, e1, ha]
      group
    rw [e2]
    exact hcomm _ (P.inv_mem hsxP) _ (P.inv_mem hx)
  have hσa : c * a * c⁻¹ = a * f₀ := by rw [hf₀]; group
  set k := a * b * a⁻¹ * b⁻¹ with hk
  have hkΦ : k ∈ Φ := hcomm a haP b hbP
  have hσk : c * k * c⁻¹ = k := by rw [hcΦ k hkΦ, mul_inv_cancel_right]
  have hσk' : c * k * c⁻¹ = k⁻¹ := by
    have hfb : f₀ * b⁻¹ = b⁻¹ * f₀ := hZ f₀ hf₀Φ _ (P.inv_mem hbP)
    have hkb : k⁻¹ * b = b * k⁻¹ := hZ _ (Φ.inv_mem hkΦ) b hbP
    calc c * k * c⁻¹
        = (c * a * c⁻¹) * (c * b * c⁻¹) * (c * a * c⁻¹)⁻¹ * (c * b * c⁻¹)⁻¹ := by
          rw [hk]; group
      _ = (a * f₀) * b⁻¹ * (a * f₀)⁻¹ * b⁻¹⁻¹ := by rw [hσa, hσb]
      _ = a * (f₀ * b⁻¹) * f₀⁻¹ * a⁻¹ * b := by group
      _ = a * (b⁻¹ * f₀) * f₀⁻¹ * a⁻¹ * b := by rw [hfb]
      _ = b⁻¹ * (b * a * b⁻¹ * a⁻¹) * b := by group
      _ = b⁻¹ * (k⁻¹ * b) := by rw [hk]; group
      _ = b⁻¹ * (b * k⁻¹) := by rw [hkb]
      _ = k⁻¹ := by group
  have hk1 : k = 1 := by
    have hkk : k = k⁻¹ := hσk.symm.trans hσk'
    have hk3 : k ^ 3 = 1 := e.exp k (hΦP hkΦ)
    calc k = k ^ 3 * (k * k⁻¹)⁻¹ * k⁻¹ * k⁻¹ := by rw [pow_three]; group
      _ = k ^ 3 * (k * k⁻¹)⁻¹ * k⁻¹ * k := by rw [← hkk]
      _ = 1 := by rw [hk3]; group
  have hab : a * b = b * a := by
    calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
      _ = b * a := by rw [← hk, hk1, one_mul]
  have hSc : (insert a (insert b (Φ : Set G))).Pairwise Commute := by
    intro u hu w hw _
    have hcΦ' : ∀ f ∈ Φ, ∀ z ∈ P, Commute f z := fun f hf z hz => hZ f hf z hz
    rcases hu with rfl | rfl | hu <;> rcases hw with rfl | rfl | hw
    · exact Commute.refl _
    · exact hab
    · exact (hcΦ' _ hw _ haP).symm
    · exact hab.symm
    · exact Commute.refl _
    · exact (hcΦ' _ hw _ hbP).symm
    · exact hcΦ' _ hu _ haP
    · exact hcΦ' _ hu _ hbP
    · exact hcΦ' _ hu _ (hΦP hw)
  have hSP : insert a (insert b (Φ : Set G)) ⊆ P :=
    Set.insert_subset haP (Set.insert_subset hbP fun z hz => hΦP hz)
  set E := Subgroup.closure (insert a (insert b (Φ : Set G))) with hE
  have hEP : E ≤ P := (Subgroup.closure_le _).mpr hSP
  have hEc := Subgroup.isMulCommutative_closure hSc
  have hEne : E ≠ P := by
    intro hEq
    have hPc : ∀ u v : ↥P, u * v = v * u := fun u v => Subtype.ext (by
      have hu : (u : G) ∈ E := by rw [hEq]; exact u.2
      have hv : (v : G) ∈ E := by rw [hEq]; exact v.2
      have h1 := congrArg Subtype.val (hEc.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
      simpa using h1)
    have hΦb : frattini ↥P = ⊥ := (CFSG.SectionRank.Ccomm.frattini_eq_bot_iff hPp).mpr
      ⟨hPc, fun u => Subtype.ext (by simpa using e.exp u u.2)⟩
    have h3 := e.cardΦ
    rw [hΦb, Subgroup.map_bot, Subgroup.card_bot] at h3
    exact absurd h3 (by norm_num)
  have hE9 : Nat.card E ≤ 9 := by
    have h1 : Nat.card E ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← e.cardP]
      exact Subgroup.card_dvd_of_le hEP
    have h2 : Nat.card E < 27 := by
      rw [← e.cardP]
      exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hEP hEne)
    obtain ⟨j, hj, hEj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    rw [hEj] at h2 ⊢
    have hj2 : j ≤ 2 := by
      by_contra h3
      push Not at h3
      have h4 : j = 3 := by omega
      subst h4
      norm_num at h2
    calc 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hj2
      _ = 9 := by norm_num
  set F := Subgroup.closure (insert a (Φ : Set G)) with hF
  have hFE : F ≤ E := Subgroup.closure_mono (Set.insert_subset_insert (Set.subset_insert _ _))
  have hΦF : Φ ≤ F := fun z hz => Subgroup.subset_closure (Set.mem_insert_of_mem _ hz)
  have haF : a ∈ F := Subgroup.subset_closure (Set.mem_insert _ _)
  have hΦlt : Φ < F := lt_of_le_of_ne hΦF fun h0 => haΦ (h0 ▸ haF)
  have hF9 : 9 ≤ Nat.card F := by
    obtain ⟨j, hj⟩ := (hPp.to_le (hFE.trans hEP)).exists_card_eq
    have h1 := Subgroup.card_lt_of_lt hΦlt
    rw [e.cardΦ, hj] at h1
    rw [hj]
    have h2 : 1 < j := by
      by_contra h3
      push Not at h3
      interval_cases j <;> norm_num at h1
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h2
  have hFeq : F = E := Subgroup.eq_of_le_of_card_ge hFE (by omega)
  have hbF : b ∈ F := by
    rw [hFeq]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hrep : ∀ z ∈ F, ∃ j : ℤ, ∃ f ∈ Φ, z = a ^ j * f := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | hz
      · exact ⟨1, 1, Φ.one_mem, by simp⟩
      · exact ⟨0, z, hz, by simp⟩
    | one => exact ⟨0, 1, Φ.one_mem, by simp⟩
    | mul u w _ _ ihu ihw =>
      obtain ⟨j, f, hf, rfl⟩ := ihu
      obtain ⟨j', f', hf', rfl⟩ := ihw
      refine ⟨j + j', f * f', Φ.mul_mem hf hf', ?_⟩
      have hfa : f * a ^ j' = a ^ j' * f := hZ f hf _ (P.zpow_mem haP j')
      calc a ^ j * f * (a ^ j' * f') = a ^ j * (f * a ^ j') * f' := by group
        _ = a ^ j * (a ^ j' * f) * f' := by rw [hfa]
        _ = a ^ (j + j') * (f * f') := by rw [zpow_add]; group
    | inv u _ ihu =>
      obtain ⟨j, f, hf, rfl⟩ := ihu
      refine ⟨-j, f⁻¹, Φ.inv_mem hf, ?_⟩
      have hfa : f⁻¹ * a ^ (-j) = a ^ (-j) * f⁻¹ := hZ _ (Φ.inv_mem hf) _ (P.zpow_mem haP _)
      calc (a ^ j * f)⁻¹ = f⁻¹ * a ^ (-j) := by rw [mul_inv_rev, zpow_neg]
        _ = a ^ (-j) * f⁻¹ := hfa
  obtain ⟨j, f, hf, hbe⟩ := hrep b hbF
  have hσb' : c * b * c⁻¹ = a ^ j * f₀ ^ j * f := by
    have hfa : Commute a f₀ := (hZ f₀ hf₀Φ a haP).symm
    have h1 : c * a ^ j * c⁻¹ = (c * a * c⁻¹) ^ j := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    rw [hbe]
    calc c * (a ^ j * f) * c⁻¹ = (c * a ^ j * c⁻¹) * (c * f * c⁻¹) := by group
      _ = (a * f₀) ^ j * f := by rw [h1, hσa, hcΦ f hf, mul_inv_cancel_right]
      _ = a ^ j * f₀ ^ j * f := by rw [hfa.mul_zpow]
  have hb2 : b⁻¹ * b⁻¹ ∈ Φ := by
    have e1 : b⁻¹ * b⁻¹ = (c * b * c⁻¹) * b⁻¹ := by rw [hσb]
    rw [e1, hσb', hbe]
    have hfj : f₀ ^ j * f * f⁻¹ * (a ^ j)⁻¹ = (a ^ j)⁻¹ * f₀ ^ j := by
      have := hZ _ (Φ.zpow_mem hf₀Φ j) _ (P.inv_mem (P.zpow_mem haP j))
      calc f₀ ^ j * f * f⁻¹ * (a ^ j)⁻¹ = f₀ ^ j * (a ^ j)⁻¹ := by group
        _ = (a ^ j)⁻¹ * f₀ ^ j := this
    have e3 : a ^ j * f₀ ^ j * f * (a ^ j * f)⁻¹ = f₀ ^ j := by
      calc a ^ j * f₀ ^ j * f * (a ^ j * f)⁻¹ = a ^ j * (f₀ ^ j * f * f⁻¹ * (a ^ j)⁻¹) := by
            group
        _ = a ^ j * ((a ^ j)⁻¹ * f₀ ^ j) := by rw [hfj]
        _ = f₀ ^ j := by group
    rw [e3]
    exact Φ.zpow_mem hf₀Φ j
  apply hbΦ
  have h1 := hsqΦ b⁻¹ (P.inv_mem hbP) hb2
  simpa using Φ.inv_mem h1


theorem mem_or_of_inv (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (e : Extra3 T L V H P U I h)
    {m : G} (hmT : m ∈ T) (hmP : m ∈ Subgroup.normalizer (P : Set G))
    (hminv : ∀ x ∈ P, m * x * m⁻¹ * x ∈ (frattini ↥P).map P.subtype)
    {c : G} (hcT : c ∈ T) (hc2 : c * c ∈ pCoreOf 2 H)
    (hcΦ : ∀ f ∈ (frattini ↥P).map P.subtype, c * f = f * c) :
    c ∈ pCoreOf 2 H ∨ c * m⁻¹ ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, -, -, hhP, hhM, -⟩ := e.pre
  set Q := pCoreOf 2 H with hQ
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  have hP1 : P ≠ ⊥ := fun h0 => hh1 (by rw [h0] at hhP; exact Subgroup.mem_bot.mp hhP)
  have hmin := Lem7.minParabolic h331 e.hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hQT : Q ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hT2 : IsPGroup 2 ↥T := hmin.isSylow.2.1
  have hO2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hHO : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hconjO : ∀ g ∈ H, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hHO hg) y).mp hy
  have hΦP : Φ ≤ P := frattini_map_le P
  have hPO : ∀ y ∈ P, y ∈ Q → y = 1 := fun y hyP hyO =>
    eq_one_of_mem_of_mem hp hp2 hPp hO2 hyP hyO
  have hcommW := e.comm_mem_W h331 h1222
  have hWQ : conjClosure (V ⊓ Q) P ≤ Q := fun w hw => (e.W_le_center hw).1
  have hkey : ∀ d ∈ T, d ∈ Subgroup.normalizer (P : Set G) →
      (∀ x ∈ P, d * x * d⁻¹ * x⁻¹ ∈ Φ) → d ∈ Q := by
    intro d hdT hdP hdΦ
    obtain ⟨j, hj⟩ := hT2 ⟨d, hdT⟩
    have hj' : d ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hdc := conj_eq_of_frattini hp hp2 hPp hdP (k := j) (fun x _ => by rw [hj']; group)
      hdΦ
    refine e.mem_of_comm h331 d hdT fun x hx => ?_
    calc d * x = (d * x * d⁻¹) * d := by group
      _ = x * d := by rw [hdc x hx]
  obtain ⟨q, hq, hqc⟩ := exists_mul_mem_normalizer h331 e.hyp hHs hsol hp hp2 hPp hPH hPi hP1
    (hTH hcT)
  have hc'T : q * c ∈ T := T.mul_mem (hQT hq) hcT
  have hc'Φ : ∀ f ∈ Φ, (q * c) * f = f * (q * c) := by
    intro f hf
    have h1 : (q * c) * f * (q * c)⁻¹ ∈ Φ := conj_mem_frattini hqc hf
    have h2 : f⁻¹ * q * f⁻¹⁻¹ * q⁻¹ ∈ conjClosure (V ⊓ Q) P :=
      hcommW _ (P.inv_mem (hΦP hf)) q hq
    have e1 : (q * c) * f * (q * c)⁻¹ = q * f * q⁻¹ := by
      calc (q * c) * f * (q * c)⁻¹ = q * (c * f) * c⁻¹ * q⁻¹ := by group
        _ = q * (f * c) * c⁻¹ * q⁻¹ := by rw [hcΦ f hf]
        _ = q * f * q⁻¹ := by group
    have h3 : f⁻¹ * (q * f * q⁻¹) ∈ Φ := by
      rw [← e1]
      exact Φ.mul_mem (Φ.inv_mem hf) h1
    have h4 : f⁻¹ * (q * f * q⁻¹) ∈ Q := by
      have e2 : f⁻¹ * (q * f * q⁻¹) = f⁻¹ * q * f⁻¹⁻¹ * q⁻¹ := by group
      rw [e2]
      exact hWQ h2
    have h5 := hPO _ (hΦP h3) h4
    have h6 : q * f * q⁻¹ = f := by
      calc q * f * q⁻¹ = f * (f⁻¹ * (q * f * q⁻¹)) := by group
        _ = f := by rw [h5, mul_one]
    calc (q * c) * f = ((q * c) * f * (q * c)⁻¹) * (q * c) := by group
      _ = f * (q * c) := by rw [e1, h6]
  have hc'2 : ∀ x ∈ P, ((q * c) * (q * c)) * x * ((q * c) * (q * c))⁻¹ = x := by
    have hsqQ : (q * c) * (q * c) ∈ Q := by
      have e1 : (q * c) * (q * c) = q * (c * q * c⁻¹) * (c * c) := by group
      rw [e1]
      exact Q.mul_mem (Q.mul_mem hq (hconjO c (hTH hcT) q hq)) hc2
    have hqcP : ∀ x ∈ P, (q * c) * x * (q * c)⁻¹ ∈ P := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp hqc x).mp hx
    intro x hx
    have h1 : ((q * c) * (q * c)) * x * ((q * c) * (q * c))⁻¹ * x⁻¹ ∈ P := by
      have e1 : ((q * c) * (q * c)) * x * ((q * c) * (q * c))⁻¹ =
          (q * c) * ((q * c) * x * (q * c)⁻¹) * (q * c)⁻¹ := by group
      rw [e1]
      exact P.mul_mem (hqcP _ (hqcP x hx)) (P.inv_mem hx)
    have h2 : ((q * c) * (q * c)) * x * ((q * c) * (q * c))⁻¹ * x⁻¹ ∈ Q := by
      have e1 : ((q * c) * (q * c)) * x * ((q * c) * (q * c))⁻¹ * x⁻¹ =
          ((q * c) * (q * c)) * (x * ((q * c) * (q * c))⁻¹ * x⁻¹) := by group
      rw [e1]
      exact Q.mul_mem hsqQ (hconjO x (hPH hx) _ (Q.inv_mem hsqQ))
    exact mul_inv_eq_one.mp (hPO _ h1 h2)
  rcases e.inv_or_triv hqc hc'Φ hc'2 with h1 | h1
  ·
    left
    have h2 := hkey _ hc'T hqc h1
    have e1 : c = q⁻¹ * (q * c) := by group
    rw [e1]
    exact Q.mul_mem (Q.inv_mem hq) h2
  ·
    right
    have hdT : q * c * m⁻¹ ∈ T := T.mul_mem hc'T (T.inv_mem hmT)
    have hdP : q * c * m⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
      Subgroup.mul_mem _ hqc (Subgroup.inv_mem _ hmP)
    have hdΦ : ∀ x ∈ P, (q * c * m⁻¹) * x * (q * c * m⁻¹)⁻¹ * x⁻¹ ∈ Φ := by
      intro x hx
      have hy : m⁻¹ * x * m ∈ P := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmP) x).mp hx
        simpa using this
      have hf₁ : x * (m⁻¹ * x * m) ∈ Φ := by
        have := hminv _ hy
        have e1 : m * (m⁻¹ * x * m) * m⁻¹ * (m⁻¹ * x * m) = x * (m⁻¹ * x * m) := by group
        rwa [e1] at this
      have hf₂ : (q * c) * x⁻¹ * (q * c)⁻¹ * x⁻¹ ∈ Φ := h1 _ (P.inv_mem hx)
      have hcf : (q * c) * (x * (m⁻¹ * x * m)) * (q * c)⁻¹ = x * (m⁻¹ * x * m) := by
        rw [hc'Φ _ hf₁, mul_inv_cancel_right]
      have e1 : (q * c * m⁻¹) * x * (q * c * m⁻¹)⁻¹ * x⁻¹ =
          ((q * c) * x⁻¹ * (q * c)⁻¹ * x⁻¹) *
            (x * ((q * c) * (x * (m⁻¹ * x * m)) * (q * c)⁻¹) * x⁻¹) := by group
      rw [e1, hcf]
      exact Φ.mul_mem hf₂ (conj_mem_frattini (Subgroup.le_normalizer hx) hf₁)
    have h2 := hkey _ hdT hdP hdΦ
    have e1 : c * m⁻¹ = q⁻¹ * (q * c * m⁻¹) := by group
    rw [e1]
    exact Q.mul_mem (Q.inv_mem hq) h2

end Extra3

end Lem22

end CFSG.Quasithin.H13
