module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_3_split
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Recognition.M12AscKlein

public section

namespace CFSG.Quasithin

open Subgroup CFSG.GorensteinWalter

variable {X : Type} [Group X] [Finite X] {V : Subgroup X} {z y : X}

namespace KleinCore

theorem sq_of_comm (h : KleinCore (⊤ : Subgroup X) V z y) {u : X} (hu2 : u * u = 1) (hu1 : u ≠ 1)
    {w : X} (hw : w * u = u * w) : w * w = 1 := by
  obtain ⟨k, -, hk⟩ := h.cent_conj (Subgroup.mem_top _) hu2 hu1
  have hV : k⁻¹ * w * k ∈ V := (hk w (Subgroup.mem_top _)).1 hw
  have := h.V_sq _ hV
  calc w * w = k * ((k⁻¹ * w * k) * (k⁻¹ * w * k)) * k⁻¹ := by group
    _ = 1 := by rw [this]; group

theorem no_cyclic_even (h : KleinCore (⊤ : Subgroup X) V z y) {U : Subgroup X} (hU : IsCyclic U)
    (hev : Even (Nat.card U)) (h4 : 4 ≤ Nat.card U) : False := by
  have h2 : 2 ∣ Nat.card U := even_iff_two_dvd.1 hev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨g, hg⟩ := hU.exists_generator
  have hgo : orderOf g = Nat.card U := orderOf_eq_card_of_forall_mem_zpowers hg
  have hu2 : (u : X) * (u : X) = 1 := by
    have : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    rw [pow_two] at this
    exact congrArg Subtype.val this
  have hu1 : (u : X) ≠ 1 := by
    intro e
    have : u = 1 := Subtype.ext e
    rw [this, orderOf_one] at hu
    omega
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg u)
  have hcomm : (g : X) * (u : X) = (u : X) * (g : X) := by
    have hc : Commute g u := by rw [← hk]; exact Commute.zpow_right (Commute.refl g) k
    exact congrArg Subtype.val hc.eq
  have hgg : (g : X) * (g : X) = 1 := h.sq_of_comm hu2 hu1 hcomm
  have hgg' : g * g = 1 := Subtype.ext hgg
  have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hgg')
  have := Nat.le_of_dvd (by norm_num) this
  omega

omit [Finite X] in
theorem mem_of_sq_eq_one {L : Subgroup X} [L.Normal] (hL : Odd L.index) {x : X} (hx : x * x = 1) :
    x ∈ L := by
  have h1 : orderOf (QuotientGroup.mk x : X ⧸ L) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two, ← QuotientGroup.mk_mul, hx, QuotientGroup.mk_one])
  have h2 : orderOf (QuotientGroup.mk x : X ⧸ L) ∣ L.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h3 : Odd (orderOf (QuotientGroup.mk x : X ⧸ L)) := Odd.of_dvd_nat hL h2
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h4 | h4
  · exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 h4)
  · rw [h4] at h3
    exact absurd h3 (by decide)

theorem not_pgl2 (h : KleinCore (⊤ : Subgroup X) V z y) {F : Type} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) {L : Subgroup X} (e : ↥L ≃* PGL2 F) : False := by
  have hq : Odd (Nat.card F) := by
    obtain ⟨p, n, hp, hpo, hn, hq⟩ := hF
    rw [hq]
    exact hpo.pow
  have h8 : 8 ∣ Nat.card L := by
    rw [Nat.card_congr e.toEquiv, pgl2_card_formula]
    have hmod : Nat.card F % 8 = 1 ∨ Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5 ∨
        Nat.card F % 8 = 7 := by
      have := Nat.odd_iff.1 hq
      omega
    have hsq : Nat.card F ^ 2 % 8 = 1 := by
      rcases hmod with h1 | h1 | h1 | h1 <;> simp [pow_two, Nat.mul_mod, h1]
    have hpos : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ Finite.card_pos
    exact Dvd.dvd.mul_left (by omega) _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥L) 2 (n := 3) (by simpa using h8)
  have hmapcard : Nat.card (W.map L.subtype) = Nat.card W :=
    (Nat.card_congr (Subgroup.equivMapOfInjective W L.subtype L.subtype_injective)).symm
  have hp : IsPGroup 2 (W.map L.subtype) :=
    (IsPGroup.iff_card).2 ⟨3, by rw [hmapcard, hW]⟩
  have := h.syl _ le_top hp
  rw [hmapcard, hW] at this
  omega

theorem exists_cyclic_even {F : Type} [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (h7 : 7 ≤ Nat.card F) :
    ∃ U : Subgroup (PSL2 F), IsCyclic U ∧ Even (Nat.card U) ∧ 4 ≤ Nat.card U := by
  obtain ⟨p, f, hp, hpo, hf, hFc⟩ := hF
  have : Fact p.Prime := ⟨hp⟩
  have hqodd : Odd (Nat.card F) := by rw [hFc]; exact hpo.pow
  have hq2 : Nat.card F % 2 = 1 := Nat.odd_iff.1 hqodd
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
    Nat.gcd_eq_right (by obtain ⟨k, hk⟩ := hqodd; exact ⟨k, by omega⟩)
  rcases Nat.even_or_odd ((Nat.card F - 1) / 2) with he | ho
  · obtain ⟨U, w, hUc, hUcard, -⟩ :=
      BenderSuzuki.External.huppert_II_8_3_split_torus_reflection_data (F := F) hFc
    rw [hgcd] at hUcard
    have he' := Nat.even_iff.1 he
    exact ⟨U, hUc, Nat.even_iff.2 (by rw [hUcard]; exact he'), by rw [hUcard]; omega⟩
  · obtain ⟨S, w, hSc, hScard, -⟩ :=
      BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_reflection_data (F := F) hFc
    rw [hgcd] at hScard
    have ho' := Nat.odd_iff.1 ho
    exact ⟨S, hSc, Nat.even_iff.2 (by rw [hScard]; omega), by rw [hScard]; omega⟩

theorem card_field_le_five (h : KleinCore (⊤ : Subgroup X) V z y) {F : Type} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) {L : Subgroup X} (e : ↥L ≃* PSL2 F) :
    Nat.card F = 3 ∨ Nat.card F = 5 := by
  by_contra hcon
  push Not at hcon
  have hq3 : 3 ≤ Nat.card F := by
    obtain ⟨p, n, hp, hpo, hn, hq⟩ := hF
    rw [hq]
    have hp3 : 3 ≤ p := by
      rcases hpo with ⟨k, hk⟩
      have := hp.two_le
      omega
    exact hp3.trans (Nat.le_self_pow (by omega) p)
  have hqodd : Nat.card F % 2 = 1 := by
    obtain ⟨p, n, hp, hpo, hn, hq⟩ := hF
    rw [hq]
    exact Nat.odd_iff.1 (hpo.pow)
  have h7 : 7 ≤ Nat.card F := by omega
  obtain ⟨U, hUc, hUe, hU4⟩ := exists_cyclic_even hF h7
  let f : PSL2 F →* X := L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  have hU'c : IsCyclic (U.map f) := (Subgroup.equivMapOfInjective U f hf).isCyclic.mp hUc
  have hcard : Nat.card (U.map f) = Nat.card U := Subgroup.card_map_of_injective hf
  exact h.no_cyclic_even hU'c (by rw [hcard]; exact hUe) (by rw [hcard]; exact hU4)

theorem eq_top_of_involution_count (h : KleinCore (⊤ : Subgroup X) V z y) {L : Subgroup X}
    [L.Normal] (hL : Odd L.index) (N : ℕ) (hLcard : Nat.card L = 4 * N)
    (hinv : Nat.card {x : ↥L // x * x = 1 ∧ x ≠ 1} ≤ N) : L = ⊤ := by
  have hCz : Nat.card (Subgroup.centralizer ({z} : Set X)) = 4 := by
    apply le_antisymm
    · rw [← h.V_card]
      apply Subgroup.card_le_of_le
      intro k hk
      exact h.cent k (Subgroup.mem_top _) (Subgroup.mem_centralizer_singleton_iff.1 hk)
    · rw [← h.V_card]
      apply Subgroup.card_le_of_le
      intro v hv
      exact Subgroup.mem_centralizer_singleton_iff.2 (h.V_comm h.z_mem hv |>.symm)
  have hmain := CFSG.ShultStronglyClosedTI.InvolutionCounting.card_centralizer_mul_card_conjugatesOf z
  rw [hCz] at hmain
  have hmemL : ∀ c ∈ conjugatesOf z, c ∈ L := by
    intro c hc
    have hc' : IsConj z c := hc
    obtain ⟨g, hg⟩ := isConj_iff.1 hc'
    apply mem_of_sq_eq_one hL
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.z_sq]; group
  have hsq : ∀ c ∈ conjugatesOf z, c * c = 1 := by
    intro c hc
    have hc' : IsConj z c := hc
    obtain ⟨g, hg⟩ := isConj_iff.1 hc'
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.z_sq]; group
  have hne : ∀ c ∈ conjugatesOf z, c ≠ 1 := by
    intro c hc
    have hc' : IsConj z c := hc
    obtain ⟨g, hg⟩ := isConj_iff.1 hc'
    rw [← hg]
    intro e
    apply h.z_ne
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group
  have hinj : Nat.card (conjugatesOf z) ≤ Nat.card {x : ↥L // x * x = 1 ∧ x ≠ 1} := by
    refine Nat.card_le_card_of_injective
      (fun c => (⟨⟨(c : X), hmemL c c.2⟩, Subtype.ext (hsq c c.2),
        fun e => hne c c.2 (congrArg Subtype.val e)⟩ : {x : ↥L // x * x = 1 ∧ x ≠ 1})) ?_
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun w : {x : ↥L // x * x = 1 ∧ x ≠ 1} => ((w : ↥L) : X)) hab
  have hle : Nat.card X ≤ Nat.card L := by omega
  exact Subgroup.eq_top_of_card_eq L (le_antisymm (Subgroup.card_le_card_group L) hle)

end KleinCore

end CFSG.Quasithin
