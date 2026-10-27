module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTwoPart

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private noncomputable def ggQ2s08t1b_restrict {G : Type} [Group G] {Bs : Subgroup G}
    (D' : Subgroup ↥Bs) (t : MulAut ↥Bs) (hDt : Subgroup.map t.toMonoidHom D' = D') :
    MulAut ↥D' :=
  (Subgroup.equivMapOfInjective D' t.toMonoidHom t.injective).trans
    (MulEquiv.subgroupCongr hDt)

private theorem ggQ2s08t1b_restrict_apply {G : Type} [Group G] {Bs : Subgroup G}
    (D' : Subgroup ↥Bs) (t : MulAut ↥Bs) (hDt : Subgroup.map t.toMonoidHom D' = D')
    (x : ↥D') : ((ggQ2s08t1b_restrict D' t hDt x : ↥D') : ↥Bs) = t x := rfl

private theorem ggQ2s08t1b_restrict_mul {G : Type} [Group G] {Bs : Subgroup G}
    (D' : Subgroup ↥Bs) (s t : MulAut ↥Bs)
    (hs : Subgroup.map s.toMonoidHom D' = D') (ht : Subgroup.map t.toMonoidHom D' = D')
    (hst : Subgroup.map (s * t).toMonoidHom D' = D') :
    ggQ2s08t1b_restrict D' (s * t) hst =
      ggQ2s08t1b_restrict D' s hs * ggQ2s08t1b_restrict D' t ht := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  change (ggQ2s08t1b_restrict D' (s * t) hst x : ↥Bs) =
    ((ggQ2s08t1b_restrict D' s hs) ((ggQ2s08t1b_restrict D' t ht) x) : ↥Bs)
  rw [ggQ2s08t1b_restrict_apply, ggQ2s08t1b_restrict_apply, ggQ2s08t1b_restrict_apply,
    MulAut.mul_apply]

private theorem ggQ2s08t1b_restrict_one {G : Type} [Group G] {Bs : Subgroup G}
    (D' : Subgroup ↥Bs) (hD1 : Subgroup.map (1 : MulAut ↥Bs).toMonoidHom D' = D')
    (x : ↥D') : ggQ2s08t1b_restrict D' 1 hD1 x = x := by
  apply Subtype.ext
  rw [ggQ2s08t1b_restrict_apply]
  rfl

private theorem ggQ2s08t1b_restrict_fixes {G : Type} [Group G] {Bs : Subgroup G}
    (D' : Subgroup ↥Bs) (t : MulAut ↥Bs) (hDt : Subgroup.map t.toMonoidHom D' = D')
    (x : ↥D') (hx : t (x : ↥Bs) = (x : ↥Bs)) : ggQ2s08t1b_restrict D' t hDt x = x := by
  apply Subtype.ext
  rw [ggQ2s08t1b_restrict_apply]
  exact hx

theorem ggQ2s08_two_part {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p = 3) {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) {Z S : Subgroup G} (hZS : Z ≤ S) (hSBs : S ≤ Bs)
    (hSZ : Nat.card ↥S ≤ p * Nat.card ↥Z) (A : Subgroup (MulAut ↥Bs))
    (hA : ∀ ν ∈ A, (∀ b : ↥Bs, (b : G) ∈ Z → ν b = b) ∧
      ∀ b : ↥Bs, ((b⁻¹ * ν b : ↥Bs) : G) ∈ S) :
    ¬ 4 ∣ Nat.card ↥A := by
  subst hp
  intro hA4
  let S' : Subgroup ↥Bs := S.subgroupOf Bs
  let Zb : Subgroup ↥Bs := Z.subgroupOf Bs
  have hZbS' : Zb ≤ S' := fun z hz => hZS hz
  let Z' : Subgroup ↥S' := Zb.subgroupOf S'
  have hcomm : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBs.1.is_comm.comm a b
  letI : CommGroup ↥Bs := { mul_comm := hcomm }
  letI : CommGroup ↥S' :=
    { mul_comm := fun a b => Subtype.ext (hcomm (a : ↥Bs) (b : ↥Bs)) }
  haveI : Z'.Normal := Subgroup.normal_of_comm Z'
  have hSshift : ∀ t ∈ A, ∀ b : ↥Bs, b⁻¹ * t b ∈ S' := by
    intro t ht b
    rw [Subgroup.mem_subgroupOf]
    exact (hA t ht).2 b
  have hSinv : ∀ t ∈ A, Subgroup.map t.toMonoidHom S' = S' := by
    intro t ht
    have hle : Subgroup.map t.toMonoidHom S' ≤ S' := by
      rintro _ ⟨d, hd, rfl⟩
      have hmem : d⁻¹ * t d ∈ S' := hSshift t ht d
      change t d ∈ S'
      rw [show t d = d * (d⁻¹ * t d) by group]
      exact S'.mul_mem hd hmem
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective t.injective])
  let W : Subgroup ↥Bs := Subgroup.map S'.subtype Z'
  have hWZb : W ≤ Zb := by
    rintro _ ⟨z, hz, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hz
  have hWle : W ≤ S' := by
    rintro _ ⟨z, hz, rfl⟩
    exact z.2
  have hZmap : ∀ t : A,
      Subgroup.map (↑(ggQ2s08t1b_restrict S' (t : MulAut ↥Bs) (hSinv t t.2)) :
        ↥S' →* ↥S') Z' = Z' := by
    intro t
    have hfix : ∀ (z : ↥S') (hz : z ∈ Z'),
        (ggQ2s08t1b_restrict S' (t : MulAut ↥Bs) (hSinv t t.2)) z = z := by
      intro z hz
      apply ggQ2s08t1b_restrict_fixes
      exact (hA (t : MulAut ↥Bs) t.2).1 (z : ↥Bs)
        (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hz))
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      change (ggQ2s08t1b_restrict S' (t : MulAut ↥Bs) (hSinv t t.2)) z ∈ Z'
      rw [hfix z hz]
      exact hz
    · intro z hz
      exact ⟨z, hz, hfix z hz⟩
  let ρ : A →* MulAut (↥S' ⧸ Z') :=
  { toFun := fun t =>
      QuotientGroup.congr Z' Z'
        (ggQ2s08t1b_restrict S' (t : MulAut ↥Bs) (hSinv t t.2)) (hZmap t)
    map_one' := by
      refine MulEquiv.ext fun x => ?_
      induction x using QuotientGroup.induction_on with
      | H x =>
        rw [QuotientGroup.congr_mk]
        change (QuotientGroup.mk ((ggQ2s08t1b_restrict S' (1 : MulAut ↥Bs)
            (hSinv 1 A.one_mem)) x) : ↥S' ⧸ Z') = QuotientGroup.mk x
        rw [ggQ2s08t1b_restrict_one]
    map_mul' := by
      intro s t
      refine MulEquiv.ext fun x => ?_
      induction x using QuotientGroup.induction_on with
      | H x =>
        rw [QuotientGroup.congr_mk, MulAut.mul_apply, QuotientGroup.congr_mk,
          QuotientGroup.congr_mk]
        change (QuotientGroup.mk ((ggQ2s08t1b_restrict S' (s * t : MulAut ↥Bs)
            (hSinv (s * t) (A.mul_mem s.2 t.2))) x) : ↥S' ⧸ Z') =
          QuotientGroup.mk ((ggQ2s08t1b_restrict S' (s : MulAut ↥Bs) (hSinv s s.2))
            ((ggQ2s08t1b_restrict S' (t : MulAut ↥Bs) (hSinv t t.2)) x))
        rw [ggQ2s08t1b_restrict_mul, MulAut.mul_apply] }
  have hker3 : ∀ t : A, ρ t = 1 → (t : MulAut ↥Bs) ^ 3 = 1 := by
    intro t ht
    have hmemW : ∀ d : ↥S', (d : ↥Bs)⁻¹ * ((t : MulAut ↥Bs) (d : ↥Bs)) ∈ W := by
      intro d
      have h1 : (QuotientGroup.mk ((ggQ2s08t1b_restrict S' (t : MulAut ↥Bs)
          (hSinv t t.2)) d) : ↥S' ⧸ Z') = (QuotientGroup.mk d : ↥S' ⧸ Z') := by
        have h2 := congrArg (fun f : MulAut (↥S' ⧸ Z') => f (QuotientGroup.mk d)) ht
        rw [show ρ t = QuotientGroup.congr Z' Z'
            (ggQ2s08t1b_restrict S' (t : MulAut ↥Bs) (hSinv t t.2)) (hZmap t) from rfl,
          QuotientGroup.congr_mk] at h2
        simpa using h2
      have h3 : ((ggQ2s08t1b_restrict S' (t : MulAut ↥Bs) (hSinv t t.2)) d)⁻¹ * d ∈ Z' :=
        QuotientGroup.eq.mp h1
      have h3' : d⁻¹ * ((ggQ2s08t1b_restrict S' (t : MulAut ↥Bs) (hSinv t t.2)) d) ∈ Z' := by
        have := Z'.inv_mem h3
        simpa only [mul_inv_rev, inv_inv] using this
      have h4 : (d : ↥Bs)⁻¹ * ((t : MulAut ↥Bs) (d : ↥Bs)) ∈ W := by
        have hm : S'.subtype (d⁻¹ *
            ((ggQ2s08t1b_restrict S' (t : MulAut ↥Bs) (hSinv t t.2)) d)) ∈ W :=
          Subgroup.mem_map_of_mem S'.subtype h3'
        simpa only [map_mul, map_inv, Subgroup.coe_subtype, ggQ2s08t1b_restrict_apply] using hm
      exact h4
    refine MulEquiv.ext fun b => ?_
    set T : MulAut ↥Bs := (t : MulAut ↥Bs) with hT
    obtain ⟨db, hdbeq⟩ : ∃ db : ↥S', (db : ↥Bs) = b⁻¹ * T b :=
      ⟨⟨b⁻¹ * T b, hSshift (t : MulAut ↥Bs) t.2 b⟩, rfl⟩
    have htb : T b = b * (db : ↥Bs) := by rw [hdbeq]; group
    set udb : ↥Bs := (db : ↥Bs)⁻¹ * T (db : ↥Bs) with hudbdef
    have hudbW : udb ∈ W := by rw [hudbdef]; exact hmemW db
    have htdb : T (db : ↥Bs) = (db : ↥Bs) * udb := by rw [hudbdef]; group
    have htudb : T udb = udb := by
      have hudbZb : udb ∈ Zb := hWZb hudbW
      exact (hA (t : MulAut ↥Bs) t.2).1 udb (Subgroup.mem_subgroupOf.mp hudbZb)
    have hdb3 : (db : ↥Bs) ^ 3 = 1 := by
      apply Subtype.ext
      have h := hBs.2 (db : G) (hSBs (Subgroup.mem_subgroupOf.mp db.2))
      simpa using h
    have hudb3 : udb ^ 3 = 1 := by
      apply Subtype.ext
      have h := hBs.2 (udb : G) (hSBs (Subgroup.mem_subgroupOf.mp (hWle hudbW)))
      simpa using h
    have ht2 : T (T b) = b * (db : ↥Bs) ^ 2 * udb := by
      rw [htb, map_mul, htb, htdb, pow_two]
      simp only [mul_assoc]
    have ht3 : T (T (T b)) = b := by
      rw [ht2]
      simp only [map_mul, map_pow]
      rw [htdb, htudb, htb]
      have hkey : (b * (db : ↥Bs)) * ((db : ↥Bs) * udb) ^ 2 * udb =
          b * ((db : ↥Bs) ^ 3 * udb ^ 3) := by
        rw [pow_two,
          show (db : ↥Bs) ^ 3 = (db : ↥Bs) * (db : ↥Bs) * (db : ↥Bs) by
            rw [pow_succ, pow_two],
          show udb ^ 3 = udb * udb * udb by rw [pow_succ, pow_two]]
        ac_rfl
      rw [hkey, hdb3, hudb3, one_mul, mul_one]
    have hT3 : (T : MulAut ↥Bs) ^ 3 = T * T * T := by rw [pow_succ, pow_succ, pow_one]
    rw [hT3, MulAut.mul_apply, MulAut.mul_apply]
    exact ht3
  have hQexp : ∀ x : ↥S' ⧸ Z', x ^ 3 = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H s =>
      have hs3 : s ^ 3 = 1 := by
        apply Subtype.ext
        exact Subtype.ext (hBs.2 (s : G) (hSBs (Subgroup.mem_subgroupOf.mp s.2)))
      rw [← QuotientGroup.mk_pow Z' s 3, QuotientGroup.eq_one_iff, hs3]
      exact Z'.one_mem
  have hMA : Nat.card (MulAut (↥S' ⧸ Z')) ∣ 2 := by
    have hQpg : IsPGroup 3 (↥S' ⧸ Z') := by
      intro x
      exact ⟨1, by rw [pow_one]; exact hQexp x⟩
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hQpg
    have hQcard : Nat.card ↥S' = Nat.card (↥S' ⧸ Z') * Nat.card ↥Z' :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
    have hS'card : Nat.card ↥S' = Nat.card ↥S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSBs).toEquiv
    have hZ'card : Nat.card ↥Z' = Nat.card ↥Z := by
      calc Nat.card ↥Z' = Nat.card ↥Zb :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZbS').toEquiv
        _ = Nat.card ↥Z :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hZS.trans hSBs)).toEquiv
    have hq_le : Nat.card (↥S' ⧸ Z') ≤ 3 := by
      have hle : Nat.card (↥S' ⧸ Z') * Nat.card ↥Z' ≤ 3 * Nat.card ↥Z' := by
        rw [← hQcard, hS'card, hZ'card]
        exact hSZ
      exact Nat.le_of_mul_le_mul_right hle Nat.card_pos
    have hnle : n ≤ 1 := by
      have h3 : 3 ^ n ≤ 3 ^ 1 := by
        rw [pow_one]
        rwa [hn] at hq_le
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h3
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · have h1 : Nat.card (↥S' ⧸ Z') = 1 := by rw [hn, pow_zero]
      haveI : Subsingleton (↥S' ⧸ Z') := (Nat.card_eq_one_iff_unique.mp h1).1
      have hsub : Subsingleton (MulAut (↥S' ⧸ Z')) :=
        ⟨fun a b => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
      have hcard1 : Nat.card (MulAut (↥S' ⧸ Z')) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
      rw [hcard1]
      exact one_dvd 2
    · have h3 : Nat.card (↥S' ⧸ Z') = 3 := by rw [hn, pow_one]
      haveI : IsCyclic (↥S' ⧸ Z') := isCyclic_of_prime_card (p := 3) h3
      have hcard2 : Nat.card (MulAut (↥S' ⧸ Z')) = 2 := by
        rw [IsCyclic.card_mulAut, h3, Nat.totient_prime (by norm_num)]
      simpa [hcard2] using (dvd_rfl : 2 ∣ 2)
  have hK3 : IsPGroup 3 (MonoidHom.ker ρ) := by
    intro t
    refine ⟨1, ?_⟩
    have ht : ρ (t : A) = 1 := t.2
    have h3 : ((t : A) : MulAut ↥Bs) ^ 3 = 1 := hker3 (t : A) ht
    exact Subtype.ext (Subtype.ext (by simpa using h3))
  have hJdvd : Nat.card (MonoidHom.range ρ) ∣ 2 := by
    have h := Subgroup.card_dvd_of_le (le_top : MonoidHom.range ρ ≤ ⊤)
    rw [Subgroup.card_top] at h
    exact dvd_trans h hMA
  have hcard : Nat.card ↥A = Nat.card (MonoidHom.ker ρ) * Nat.card (MonoidHom.range ρ) :=
    (Subgroup.card_ker_mul_card_range ρ).symm
  have h4' : 4 ∣ Nat.card (MonoidHom.ker ρ) * Nat.card (MonoidHom.range ρ) := by
    rw [← hcard]; exact hA4
  have hKcop : Nat.Coprime 2 (Nat.card (MonoidHom.ker ρ)) := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hK3
    rw [hn]
    exact (show Nat.Coprime 2 3 by norm_num).pow_right n
  have h4r : 4 ∣ Nat.card (MonoidHom.range ρ) :=
    (hKcop.pow_left 2).dvd_of_dvd_mul_right (by rw [Nat.mul_comm]; exact h4')
  have hle2 : Nat.card (MonoidHom.range ρ) ≤ 2 := Nat.le_of_dvd (by norm_num) hJdvd
  have h4le : 4 ≤ Nat.card (MonoidHom.range ρ) := Nat.le_of_dvd Nat.card_pos h4r
  omega

end CFSG.StandardType

end
