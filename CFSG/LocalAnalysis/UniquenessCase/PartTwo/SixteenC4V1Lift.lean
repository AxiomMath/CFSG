module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Setup
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s16c4v1_fix_of_induces_fix (S : s16c4v1_Sit D V L hV) {m : G} (hm : m ∈ D.M)
    (hodd : Odd (orderOf m)) (hV1 : ∀ x ∈ v1Sub D.M ⊥ V hV L, m * x * m⁻¹ = x)
    {γ : ↥(SUid S.F.σ 4)} (hγ : s16c4v1_Induces S m γ) {v : G} (hv : v ∈ V)
    (hfix : γ • s16c4v1_vec S v = s16c4v1_vec S v) : m * v * m⁻¹ = v := by
  set c : G := m * v * m⁻¹ * v⁻¹ with hc
  have hmv : m * v * m⁻¹ ∈ V := s16c4v1_conj_mem S hm hv
  have hcV : c ∈ V := by
    rw [hc]; exact V.mul_mem hmv (V.inv_mem hv)
  have hvinv : v⁻¹ = v := by
    have h2 : v * v = 1 := by simpa [pow_two] using hV.2 v hv
    exact inv_eq_of_mul_eq_one_right h2
  have hsum : s16c4v1_vec S v + s16c4v1_vec S v = 0 := by
    ext i
    rw [Pi.add_apply, Pi.zero_apply, ← two_mul, S.F.two_eq_zero, zero_mul]
  have hvec : s16c4v1_vec S c = 0 := by
    rw [hc, s16c4v1_vec_mul S hmv (V.inv_mem hv),
      show s16c4v1_vec S v⁻¹ = s16c4v1_vec S v from by rw [hvinv],
      hγ v hv, hfix, hsum]
  have hcV1 : c ∈ v1Sub D.M ⊥ V hV L := (s16c4v1_vec_eq_zero_iff S hcV).1 hvec
  have hfixc : m * c * m⁻¹ = c := hV1 c hcV1
  have hcv : m * v * m⁻¹ = c * v := by rw [hc]; group
  have hstep : ∀ j : ℕ, m ^ j * v * (m ^ j)⁻¹ = c ^ j * v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc m ^ (j + 1) * v * (m ^ (j + 1))⁻¹
          = m * (m ^ j * v * (m ^ j)⁻¹) * m⁻¹ := by rw [pow_succ']; group
        _ = m * (c ^ j * v) * m⁻¹ := by rw [ih]
        _ = (m * c ^ j * m⁻¹) * (m * v * m⁻¹) := by group
        _ = ((m * c * m⁻¹) ^ j) * (m * v * m⁻¹) := by rw [conj_pow]
        _ = c ^ j * (c * v) := by rw [hfixc, hcv]
        _ = c ^ (j + 1) * v := by rw [pow_succ]; group
  have hcn : c ^ orderOf m = 1 := by
    have h2 := hstep (orderOf m)
    rw [pow_orderOf_eq_one] at h2
    simp only [one_mul, inv_one, mul_one] at h2
    exact mul_right_cancel (by rw [one_mul]; exact h2.symm)
  have hc2 : c ^ 2 = 1 := hV.2 c hcV
  have hdvd2 : orderOf c ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 hc2
  have hdvdn : orderOf c ∣ orderOf m := orderOf_dvd_iff_pow_eq_one.2 hcn
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h1 | h1
  · rw [hcv, orderOf_eq_one_iff.1 h1, one_mul]
  · exact absurd (even_iff_two_dvd.2 (h1 ▸ hdvdn)) (Nat.not_even_iff_odd.2 hodd)

theorem s16c4v1_lift_subgroup (S : s16c4v1_Sit D V L hV) {E : Subgroup ↥(SUid S.F.σ 4)}
    (hE : IsPGroup 3 E) :
    ∃ P : Subgroup G, P ≤ L ∧ IsPGroup 3 P ∧
      (∀ γ ∈ E, ∃ p ∈ P, s16c4v1_Induces S p γ) ∧
      (∀ p ∈ P, ∃ γ ∈ E, s16c4v1_Induces S p γ) := by
  classical
  let ψ : ↥L →* ↥(SUid S.F.σ 4) :=
    { toFun := fun l => Classical.choose (s16c4v1_induces_of_mem_L S l.2)
      map_one' := by
        apply s16c4v1_induces_unique S
        · exact Classical.choose_spec (s16c4v1_induces_of_mem_L S (1 : ↥L).2)
        · intro w hw; simp [s16c4v1_Induces]
      map_mul' := fun a b => by
        apply s16c4v1_induces_unique S
        · exact Classical.choose_spec (s16c4v1_induces_of_mem_L S (a * b).2)
        · exact s16c4v1_induces_mul S (S.sect.setting.hyp151.le a.2)
            (S.sect.setting.hyp151.le b.2)
            (Classical.choose_spec (s16c4v1_induces_of_mem_L S a.2))
            (Classical.choose_spec (s16c4v1_induces_of_mem_L S b.2)) }
  have hψsurj : Function.Surjective ψ := by
    intro γ
    obtain ⟨l, hl, hγ⟩ := s16c4v1_exists_induces S γ
    refine ⟨⟨l, hl⟩, ?_⟩
    exact s16c4v1_induces_unique S
      (Classical.choose_spec (s16c4v1_induces_of_mem_L S hl)) hγ
  let H : Subgroup ↥L := E.comap ψ
  let ψH : ↥H →* ↥E :=
    { toFun := fun q => ⟨ψ (q : ↥L), q.2⟩
      map_one' := Subtype.ext (by simpa using map_one ψ)
      map_mul' := fun a b => Subtype.ext (by simpa using map_mul ψ a b) }
  have hψHsurj : Function.Surjective ψH := by
    intro γ
    obtain ⟨l, hl⟩ := hψsurj γ
    refine ⟨⟨l, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, hl]; exact γ.2
    · apply Subtype.ext
      show ψ l = γ
      exact hl
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 3 ↥H) := Sylow.nonempty
  have hEtop : IsPGroup 3 (⊤ : Subgroup ↥E) := hE.to_subgroup ⊤
  have hmax : (⊤ : Subgroup ↥E) = (Q : Subgroup ↥H).map ψH :=
    (Q.mapSurjective hψHsurj).is_maximal' hEtop le_top
  have htop : (Q : Subgroup ↥H).map ψH = ⊤ := hmax.symm
  let f : ↥H →* G := (Subgroup.subtype L).comp (Subgroup.subtype H)
  refine ⟨(Q : Subgroup ↥H).map f, ?_, Q.2.map f, ?_, ?_⟩
  · rintro _ ⟨q, -, rfl⟩
    exact (q : ↥L).2
  · intro γ hγ
    have hmem : (⟨γ, hγ⟩ : ↥E) ∈ (⊤ : Subgroup ↥E) := Subgroup.mem_top _
    rw [← htop] at hmem
    obtain ⟨q, hqQ, hqeq⟩ := Subgroup.mem_map.1 hmem
    refine ⟨f q, Subgroup.mem_map_of_mem f hqQ, ?_⟩
    have hγeq : ψ (q : ↥L) = γ := by
      have h := congrArg Subtype.val hqeq
      exact h
    have hchoose : s16c4v1_Induces S ((q : ↥L) : G) (ψ (q : ↥L)) :=
      Classical.choose_spec (s16c4v1_induces_of_mem_L S (q : ↥L).2)
    rw [hγeq] at hchoose
    simpa [f, MonoidHom.comp_apply] using hchoose
  · rintro _ ⟨q, -, rfl⟩
    exact ⟨(ψH q : ↥E), (ψH q).2,
      Classical.choose_spec (s16c4v1_induces_of_mem_L S (q : ↥L).2)⟩

private theorem s16c4v1_lft_odd_orderOf {H : Subgroup G} {g : G} (hH : IsPGroup 3 H)
    (hg : g ∈ H) : Odd (orderOf g) := by
  obtain ⟨k, hk⟩ := (isPGroup_iff_orderOf_dvd_pow.mp hH) ⟨g, hg⟩
  rw [Subgroup.orderOf_mk g hg] at hk
  exact (show Odd (3 ^ k) from (show Odd (3 : ℕ) by decide).pow).of_dvd_nat hk

private theorem s16c4v1_lft_exists_three_induces (S : s16c4v1_Sit D V L hV)
    {γ : ↥(SUid S.F.σ 4)} (hγ1 : γ ≠ 1) (hγ3 : γ ^ 3 = 1) :
    ∃ p : G, p ∈ L ∧ p ≠ 1 ∧ IsPGroup 3 (Subgroup.zpowers p) ∧
      s16c4v1_Induces S p γ := by
  have hEp : IsPGroup 3 (Subgroup.zpowers γ) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [pow_one, Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.2 hγ3
  obtain ⟨P, hPL, hPp, hPE, -⟩ := s16c4v1_lift_subgroup S hEp
  obtain ⟨p, hpP, hpγ⟩ := hPE γ (Subgroup.mem_zpowers γ)
  have hpL : p ∈ L := hPL hpP
  have hp1 : p ≠ 1 := by
    intro hp
    refine hγ1 (s16c4v1_induces_unique S (hp ▸ hpγ) ?_)
    intro w hw
    simp [s16c4v1_Induces]
  have hpp : IsPGroup 3 (Subgroup.zpowers p) := hPp.to_le (Subgroup.zpowers_le.2 hpP)
  exact ⟨p, hpL, hp1, hpp, hpγ⟩

private theorem s16c4v1_lft_noncyclic_of_e9 (S : s16c4v1_Sit D V L hV)
    {E : Subgroup ↥(SUid S.F.σ 4)} (hEab : IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ 2) :
    ∃ P : Subgroup G, P ≤ L ∧ IsPGroup 3 P ∧ ¬ IsCyclic P ∧
      (∀ γ ∈ E, ∃ p ∈ P, s16c4v1_Induces S p γ) ∧
      (∀ p ∈ P, ∃ γ ∈ E, s16c4v1_Induces S p γ) := by
  have hEp : IsPGroup 3 E := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    exact ⟨1, by rw [pow_one]; exact Subtype.ext (hEab.2 x x.2)⟩
  obtain ⟨P, hPL, hPp, hPE, hEP⟩ := s16c4v1_lift_subgroup S hEp
  let g : ↥P → ↥E := fun p => ⟨Classical.choose (hEP p p.2),
    (Classical.choose_spec (hEP p p.2)).1⟩
  have hg : ∀ p : ↥P, ((g p : ↥E) : ↥(SUid S.F.σ 4)) = Classical.choose (hEP p p.2) :=
    fun p => rfl
  let φ : ↥P →* ↥E :=
    { toFun := g
      map_one' := by
        apply Subtype.ext
        rw [hg 1]
        exact s16c4v1_induces_unique S
          (by simpa using (Classical.choose_spec (hEP 1 (Subgroup.one_mem P))).2)
          (by intro w hw; simp [s16c4v1_Induces])
      map_mul' := fun a b => by
        apply Subtype.ext
        rw [hg (a * b)]
        change Classical.choose (hEP (a * b) (Subgroup.mul_mem P a.2 b.2)) =
          ((g a : ↥E) : ↥(SUid S.F.σ 4)) * ((g b : ↥E) : ↥(SUid S.F.σ 4))
        rw [hg a, hg b]
        exact s16c4v1_induces_unique S
          (by simpa using
            (Classical.choose_spec (hEP (a * b) (Subgroup.mul_mem P a.2 b.2))).2)
          (by
            have h := s16c4v1_induces_mul S (S.sect.setting.hyp151.le (hPL a.2))
              (S.sect.setting.hyp151.le (hPL b.2))
              (Classical.choose_spec (hEP a a.2)).2
              (Classical.choose_spec (hEP b b.2)).2
            simpa using h) }
  have hφsurj : Function.Surjective φ := by
    intro γ
    obtain ⟨p, hpP, hpγ⟩ := hPE γ γ.2
    refine ⟨⟨p, hpP⟩, ?_⟩
    apply Subtype.ext
    change Classical.choose (hEP p hpP) = (γ : ↥(SUid S.F.σ 4))
    exact s16c4v1_induces_unique S
      (by simpa using (Classical.choose_spec (hEP p hpP)).2) hpγ
  have hEnc : ¬ IsCyclic E :=
    CFSG.AGLEmbedding.BlockCyc.not_isCyclic_of_isElemAbelian_sq hEab hEcard
  refine ⟨P, hPL, hPp, ?_, hPE, hEP⟩
  intro hcyc
  have hEcyc : IsCyclic ↥E := by
    letI : IsCyclic ↥P := hcyc
    exact isCyclic_of_surjective φ hφsurj
  exact hEnc hEcyc

theorem s16c4v1_noncyclic_centralizer (S : s16c4v1_Sit D V L hV) {v : G} (hv : v ∈ V)
    (h : s16c4v1_vec S v = 0 ∨ herm S.F.σ (s16c4v1_vec S v) (s16c4v1_vec S v) ≠ 0) :
    ∃ P : Subgroup G, P ≤ D.M ∧ IsPGroup 3 P ∧ ¬ IsCyclic P ∧
      P ≤ Subgroup.centralizer ({v} : Set G) := by
  rcases h with hv0 | hns
  · have hv1 : v ∈ v1Sub D.M ⊥ V hV L := (s16c4v1_vec_eq_zero_iff S hv).1 hv0
    have hherm : herm S.F.σ (Pi.single (0 : Fin 4) (1 : S.F.K))
        (Pi.single (0 : Fin 4) (1 : S.F.K)) ≠ 0 := by
      rw [herm_single_right, Pi.single_eq_same, map_one, one_mul]
      exact one_ne_zero
    obtain ⟨E, hEab, hEcard, -⟩ :=
      s16c4v1_stab_nonsing (K := S.F.K) (σ := S.F.σ) S.F.card_K S.F.isUnitary hherm
    obtain ⟨P, hPL, hPp, hPnc, -, -⟩ := s16c4v1_lft_noncyclic_of_e9 S hEab hEcard
    exact ⟨P, fun p hp => S.sect.setting.hyp151.le (hPL hp), hPp, hPnc, fun p hp => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul).1 (s16c4v1_L_centralizes_V1 S (hPL hp) hv1)⟩
  · obtain ⟨E, hEab, hEcard, hEfix⟩ :=
      s16c4v1_stab_nonsing (K := S.F.K) (σ := S.F.σ) S.F.card_K S.F.isUnitary hns
    obtain ⟨P, hPL, hPp, hPnc, -, hEP⟩ := s16c4v1_lft_noncyclic_of_e9 S hEab hEcard
    refine ⟨P, fun p hp => S.sect.setting.hyp151.le (hPL hp), hPp, hPnc, fun p hp => ?_⟩
    obtain ⟨γ, hγE, hpγ⟩ := hEP p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine (mul_inv_eq_iff_eq_mul).1 ?_
    exact s16c4v1_fix_of_induces_fix S (S.sect.setting.hyp151.le (hPL hp))
      (s16c4v1_lft_odd_orderOf hPp hp)
      (fun x hx => s16c4v1_L_centralizes_V1 S (hPL hp) hx) hpγ hv (hEfix γ hγE)

theorem s16c4v1_exists_three_fix (S : s16c4v1_Sit D V L hV) {v : G} (hv : v ∈ V) :
    ∃ x : G, x ∈ D.M ∧ x ≠ 1 ∧ IsPGroup 3 (Subgroup.zpowers x) ∧ x * v * x⁻¹ = v := by
  rcases eq_or_ne (s16c4v1_vec S v) 0 with hv0 | hv0
  · have hv1 : v ∈ v1Sub D.M ⊥ V hV L := (s16c4v1_vec_eq_zero_iff S hv).1 hv0
    have he : (Pi.single (0 : Fin 4) (1 : S.F.K) : Fin 4 → S.F.K) ≠ 0 := by
      intro h
      have h0 : (1 : S.F.K) = 0 := by simpa using congrFun h 0
      exact one_ne_zero h0
    obtain ⟨γ, hγ1, hγ3, -⟩ :=
      s16c4v1_stab_ne_zero (K := S.F.K) (σ := S.F.σ) S.F.card_K S.F.isUnitary he
    obtain ⟨p, hpL, hp1, hpp, -⟩ := s16c4v1_lft_exists_three_induces S hγ1 hγ3
    exact ⟨p, S.sect.setting.hyp151.le hpL, hp1, hpp,
      s16c4v1_L_centralizes_V1 S hpL hv1⟩
  · obtain ⟨γ, hγ1, hγ3, hγfix⟩ :=
      s16c4v1_stab_ne_zero (K := S.F.K) (σ := S.F.σ) S.F.card_K S.F.isUnitary hv0
    obtain ⟨p, hpL, hp1, hpp, hpγ⟩ := s16c4v1_lft_exists_three_induces S hγ1 hγ3
    refine ⟨p, S.sect.setting.hyp151.le hpL, hp1, hpp, ?_⟩
    exact s16c4v1_fix_of_induces_fix S (S.sect.setting.hyp151.le hpL)
      (s16c4v1_lft_odd_orderOf hpp (Subgroup.mem_zpowers p))
      (fun x hx => s16c4v1_L_centralizes_V1 S hpL hx) hpγ hv hγfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
