module

public import CFSG.Quasithin.Background.RonanD321FiveMod
public import CFSG.Quasithin.Background.SmithD321Count

public section

namespace CFSG.Quasithin.RonanD321.Five

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391 CFSG.Open CFSG.Assembly.LowTwoRank

theorem index_dvd_card_of_stabilizer_eq {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (K : Subgroup G) (hK : ∀ x : X, MulAction.stabilizer G x = K) : K.index ∣ Nat.card X := by
  classical
  have : Fintype (MulAction.orbitRel.Quotient G X) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits G X), Nat.card_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, hK]

variable {W : Type} [CommGroup W] [Finite W]

theorem exists_ker {L : Subgroup (MulAut W)} (hexp : ∀ w : W, w ^ 2 = 1) (h2 : D321Two L)
    {S : Subgroup (MulAut W)} (hSL : ∀ s ∈ S, ∀ l ∈ L, l * s = s * l) (hS5 : IsPGroup 5 ↥S) :
    ∃ K : Subgroup ↥S, (∀ s : ↥S, s ∈ K ↔ ∀ u ∈ commV L, (s : MulAut W) u = u) ∧ K.Normal ∧
      K.index ∣ 5 := by
  classical
  obtain ⟨-, -, -, hcardU, -⟩ := exists_isotypic_of_d321Two hexp h2
  have hpres : ∀ s ∈ S, ∀ u ∈ commV L, s u ∈ commV L := fun s hs u hu =>
    B15P4.map_commV_mem (mem_normalizer_of_comm (hSL s hs)) u hu
  let K : Subgroup ↥S :=
    { carrier := {s | ∀ u ∈ commV L, (s : MulAut W) u = u}
      one_mem' := fun u _ => rfl
      mul_mem' := fun {a b} ha hb u hu => by
        show (a : MulAut W) ((b : MulAut W) u) = u
        rw [hb u hu, ha u hu]
      inv_mem' := fun {a} ha u hu => by
        show (a : MulAut W)⁻¹ u = u
        calc (a : MulAut W)⁻¹ u = (a : MulAut W)⁻¹ ((a : MulAut W) u) := by rw [ha u hu]
          _ = u := MulAut.inv_apply_self W _ u }
  have hK : ∀ s : ↥S, s ∈ K ↔ ∀ u ∈ commV L, (s : MulAut W) u = u := fun _ => Iff.rfl
  have hKn : K.Normal := by
    refine ⟨fun n hn g u hu => ?_⟩
    have hgu : (g : MulAut W)⁻¹ u ∈ commV L := hpres _ (S.inv_mem g.2) u hu
    show (g : MulAut W) ((n : MulAut W) ((g : MulAut W)⁻¹ u)) = u
    rw [hn _ hgu, MulAut.apply_inv_self]
  refine ⟨K, hK, hKn, ?_⟩
  let act : MulAction ↥S {u : ↥(commV L) // u ≠ 1} :=
    { smul := fun s x => ⟨⟨(s : MulAut W) x.1, hpres s s.2 x.1 x.1.2⟩, fun h => x.2 (by
          apply Subtype.ext
          have h' : (s : MulAut W) (x.1 : W) = 1 := congrArg Subtype.val h
          exact (map_eq_one_iff _ (s : MulAut W).injective).1 h')⟩
      one_smul := fun x => Subtype.ext (Subtype.ext rfl)
      mul_smul := fun s s' x => Subtype.ext (Subtype.ext rfl) }
  have hstab : ∀ x : {u : ↥(commV L) // u ≠ 1}, MulAction.stabilizer ↥S x = K := by
    intro x
    ext s
    rw [MulAction.mem_stabilizer_iff, hK]
    constructor
    · intro hsx
      have h1 : (s : MulAut W) (x.1 : W) = x.1 :=
        congrArg (fun z : {u : ↥(commV L) // u ≠ 1} => ((z.1 : ↥(commV L)) : W)) hsx
      obtain ⟨k, hk⟩ := hS5 s
      have hk' : (s : MulAut W) ^ (5 ^ k) = 1 := by
        rw [← Subgroup.coe_pow, hk]
        rfl
      rcases fix_or_free hexp h2 (hSL s s.2) hk' with h | h
      · exact h
      · exact absurd (h _ x.1.2 h1) fun h' => x.2 (Subtype.ext h')
    · intro hs
      exact Subtype.ext (Subtype.ext (hs _ x.1.2))
  have hX : Nat.card {u : ↥(commV L) // u ≠ 1} = 4095 := by
    have h1 := Nat.card_congr (Equiv.optionSubtypeNe (1 : ↥(commV L)))
    rw [Finite.card_option, hcardU] at h1
    norm_num at h1
    omega
  have hdvd := index_dvd_card_of_stabilizer_eq K hstab
  rw [hX] at hdvd
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : K.FiniteIndex := Subgroup.finiteIndex_of_finite
  obtain ⟨n, hn⟩ := hS5.index K
  rw [hn] at hdvd ⊢
  rcases n with _ | _ | n
  · simp
  · simp
  · exfalso
    have h25 : 5 ^ 2 ∣ 4095 := (pow_dvd_pow 5 (by omega : 2 ≤ n + 2)).trans hdvd
    norm_num at h25

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}

theorem eq_one_of_fix_commV (hB : D321Base M Mp T L V t) {x : MulAut W}
    (h1 : ∀ u ∈ commV L, x u = u) (h2 : ∀ u ∈ commV (conjAutSub t L), x u = u) : x = 1 := by
  have hle : commV L ⊔ commV (conjAutSub t L) ≤
      MonoidHom.eqLocus x.toMonoidHom (MonoidHom.id W) :=
    sup_le (fun u hu => h1 u hu) (fun u hu => h2 u hu)
  rw [← map_commV_conjAutSub, hB.commV_sup_map] at hle
  ext w
  exact hle (Subgroup.mem_top w)

theorem eq_one_of_prime_ne_five (hB : D321Base M Mp T L V t) (h2 : D321Two L) {x : MulAut W}
    (hx : x ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) (hxp : x ^ p = 1) : x = 1 := by
  by_cases hpL : p ∣ Nat.card ↥L
  · exact hB.eq_one_of_pow_prime hp hp2 hpL hx hxp
  have h168 := card_eq_168_of_isPSL32 h2.1
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hpL (by rw [h168]; norm_num)
  have hp7 : p ≠ 7 := by
    rintro rfl
    exact hpL (by rw [h168]; norm_num)
  have hfix : ∀ {X : Subgroup (MulAut W)}, D321Two X → X ≤ Mp → ∀ u ∈ commV X, x u = u := by
    intro X hX hXMp
    by_contra hcon
    push Not at hcon
    obtain ⟨u, hu, hxu⟩ := hcon
    rcases prime_cases_of_moves hB.exp hX
        (fun l hl => Subgroup.mem_centralizer_iff.1 hx.2 l (hXMp hl)) hp hp2
        (fun v _ => by rw [hxp]; rfl) ⟨u, hu, hxu⟩ with h | h | ⟨h, -⟩
    · exact hp3 h
    · exact hp7 h
    · exact hp5 h
  exact eq_one_of_fix_commV hB (hfix h2 hB.L_le_Mp) (hfix (d321Two_conjAutSub h2 t) hB.Lt_le_Mp)

theorem card_le_and_pow_five (hB : D321Base M Mp T L V t) (h2 : D321Two L)
    {S : Subgroup (MulAut W)} (hSC : S ≤ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))
    (hS5 : IsPGroup 5 ↥S) : Nat.card ↥S ≤ 25 ∧ ∀ s ∈ S, s ^ 5 = 1 := by
  have hcomm : ∀ {X : Subgroup (MulAut W)}, X ≤ Mp → ∀ s ∈ S, ∀ l ∈ X, l * s = s * l :=
    fun hX s hs l hl => Subgroup.mem_centralizer_iff.1 (hSC hs).2 l (hX hl)
  obtain ⟨K₁, hK₁, hn₁, hi₁⟩ := exists_ker hB.exp h2 (hcomm hB.L_le_Mp) hS5
  obtain ⟨K₂, hK₂, hn₂, hi₂⟩ :=
    exists_ker hB.exp (d321Two_conjAutSub h2 t) (hcomm hB.Lt_le_Mp) hS5
  have hbot : K₁ ⊓ K₂ = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    rw [Subgroup.mem_bot]
    exact Subtype.ext (eq_one_of_fix_commV hB ((hK₁ s).1 hs.1) ((hK₂ s).1 hs.2))
  refine ⟨?_, fun s hs => ?_⟩
  · have h1 := Subgroup.index_inf_le (H := K₁) (K := K₂)
    rw [hbot, Subgroup.index_bot] at h1
    have h1' := Nat.le_of_dvd (by norm_num) hi₁
    have h2' := Nat.le_of_dvd (by norm_num) hi₂
    calc Nat.card ↥S ≤ K₁.index * K₂.index := h1
      _ ≤ 5 * 5 := Nat.mul_le_mul h1' h2'
      _ = 25 := by norm_num
  · have hpow : ∀ (K : Subgroup ↥S), K.Normal → K.index ∣ 5 → (⟨s, hs⟩ : ↥S) ^ 5 ∈ K := by
      intro K hKn hK
      obtain ⟨c, hc⟩ := hK
      rw [hc, pow_mul]
      exact K.pow_mem (K.pow_index_mem _) c
    have h1 : (⟨s, hs⟩ : ↥S) ^ 5 ∈ K₁ ⊓ K₂ := ⟨hpow K₁ hn₁ hi₁, hpow K₂ hn₂ hi₂⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h3 := congrArg Subtype.val h1
    simpa using h3

end CFSG.Quasithin.RonanD321.Five
