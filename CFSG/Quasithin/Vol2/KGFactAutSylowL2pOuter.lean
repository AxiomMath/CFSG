module

public import CFSG.Quasithin.Vol2.KGFactAutSylowL2Sq
public import CFSG.Quasithin.H13.KGFact68L2p

public section

namespace CFSG.Quasithin.H13.KGAutSyl

open CFSG.QuasithinUnique CFSG.ComponentClassification.OuterAutomorphisms

theorem fix_of_comm_four {G : Type} [Group G] {P : Subgroup G} [Finite P]
    (hcard : Nat.card P = 4) (hsq : ∀ z ∈ P, z * z = 1) (f g : MulAut G)
    (hfP : ∀ z ∈ P, f z ∈ P) (hgP : ∀ z ∈ P, g z ∈ P) (hf2 : ∀ z ∈ P, f (f z) = z)
    (hf1 : ∃ z ∈ P, f z ≠ z) (hgf : ∀ z ∈ P, g (f z) = f (g z)) {m : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1) : ∀ z ∈ P, g z = z := by
  have hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    have h1 := hsq _ (P.mul_mem ha hb)
    have h2 : a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2, mul_inv_rev, inv_eq_of_mul_eq_one_left (hsq b hb), inv_eq_of_mul_eq_one_left (hsq a ha)]
  let F : Subgroup G :=
    { carrier := {u | u ∈ P ∧ f u = u}
      mul_mem' := fun {a b} ha hb => ⟨P.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
      one_mem' := ⟨P.one_mem, map_one f⟩
      inv_mem' := fun {a} ha => ⟨P.inv_mem ha.1, by rw [map_inv, ha.2]⟩ }
  have hFP : F ≤ P := fun u hu => hu.1
  obtain ⟨z₀, hz₀P, hz₀⟩ := hf1
  obtain ⟨w, hw⟩ : ∃ w, w = z₀ * f z₀ := ⟨_, rfl⟩
  have hwP : w ∈ P := hw ▸ P.mul_mem hz₀P (hfP z₀ hz₀P)
  have hfw : f w = w := by
    rw [hw, map_mul, hf2 z₀ hz₀P]
    exact hcomm _ (hfP z₀ hz₀P) _ hz₀P
  have hwF : w ∈ F := ⟨hwP, hfw⟩
  have hw1 : w ≠ 1 := by
    intro h
    apply hz₀
    have : f z₀ = z₀⁻¹ := eq_inv_of_mul_eq_one_right (by rw [← hw, h])
    rw [this, inv_eq_of_mul_eq_one_left (hsq z₀ hz₀P)]
  have huniq : ∀ u ∈ F, u ≠ 1 → u = w := by
    have : Finite F := Finite.of_injective (Subgroup.inclusion hFP)
      (Subgroup.inclusion_injective hFP)
    have hle : Nat.card F ≤ 2 := by
      have hdvd : Nat.card F ∣ 4 := by
        rw [← hcard]
        exact Subgroup.card_dvd_of_le hFP
      have hne : Nat.card F ≠ 4 := by
        intro h4
        have hFeq : F = P := Subgroup.eq_of_le_of_card_ge hFP (by rw [h4, hcard])
        exact hz₀ (hFeq ▸ hz₀P : z₀ ∈ F).2
      have := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases h : Nat.card F <;> omega
    intro u hu hu1
    have hnt : Nontrivial F := ⟨⟨1, ⟨w, hwF⟩, fun h => hw1 (congrArg Subtype.val h).symm⟩⟩
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    have h2 : Nat.card F = 2 := by omega
    obtain ⟨c, -, hc⟩ := (Nat.card_eq_two_iff' (1 : F)).mp h2
    have e1 := hc ⟨u, hu⟩ (fun h => hu1 (congrArg Subtype.val h))
    have e2 := hc ⟨w, hwF⟩ (fun h => hw1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (e1.trans e2.symm)
  have hgw : g w = w := by
    refine huniq _ ⟨hgP w hwP, ?_⟩ (fun h => hw1 (g.injective (by rw [h, map_one])))
    rw [← hgf w hwP, hfw]
  intro z hz
  by_cases hfz : f z = z
  · rcases eq_or_ne z 1 with h | h
    · rw [h, map_one]
    · rw [huniq z ⟨hz, hfz⟩ h, hgw]
  ·
    have hwz : z * f z = w := huniq _ ⟨P.mul_mem hz (hfP z hz), by
      rw [map_mul, hf2 z hz]; exact hcomm _ (hfP z hz) _ hz⟩ (fun h => hfz (by
        have : f z = z⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [this, inv_eq_of_mul_eq_one_left (hsq z hz)]))
    have hfz' : f z = z * w := by
      rw [← hwz, ← mul_assoc, hsq z hz, one_mul]
    have hvP : z * g z ∈ P := P.mul_mem hz (hgP z hz)
    have hfv : f (z * g z) = z * g z := by
      rw [map_mul, ← hgf z hz, hfz', map_mul, hgw]
      calc z * w * (g z * w) = z * g z * (w * w) := by
            rw [mul_assoc, mul_assoc, ← mul_assoc w (g z) w, hcomm w hwP (g z) (hgP z hz),
              mul_assoc (g z) w w, ← mul_assoc]
        _ = z * g z := by rw [hsq w hwP, mul_one]
    by_cases hv1 : z * g z = 1
    · have : g z = z⁻¹ := eq_inv_of_mul_eq_one_right hv1
      rw [this, inv_eq_of_mul_eq_one_left (hsq z hz)]
    · exfalso
      have hv : z * g z = w := huniq _ ⟨hvP, hfv⟩ hv1
      have hgz : g z = z * w := by
        rw [← hv, ← mul_assoc, hsq z hz, one_mul]
      have hpow : ∀ k : ℕ, (g ^ k) z = z * w ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ' g k, MulAut.mul_apply, ih, map_mul, hgz, map_pow, hgw, pow_succ' w k,
            mul_assoc]
      have h1 := hpow m
      rw [hgm, MulAut.one_apply] at h1
      obtain ⟨j, hj⟩ := hm
      have hwm : w ^ m = w := by
        rw [hj, pow_succ, pow_mul, sq, hsq w hwP, one_pow, one_mul]
      rw [hwm] at h1
      exact hw1 (mul_left_cancel (h1.symm.trans (mul_one z).symm))

theorem normalizer_inf_le_of_four {G : Type} [Group G] [Finite G]
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G))
    (hsyl : ∀ P : Subgroup G, IsSylowTwoOf P ⊤ → Nat.card P = 4 ∧ ∀ z ∈ P, z * z = 1)
    (hfix : ∀ P : Subgroup G, IsSylowTwoOf P ⊤ → ∀ α : MulAut G, (∀ z ∈ P, α z = z) →
      ∃ g ∈ P, α = MulAut.conj g)
    (hout : Nat.card (Outer G) ∣ 2) {A S : Subgroup (MulAut G)}
    (hA : (MulAut.conj : G →* MulAut G).range ≤ A)
    (hAne : A ≠ (MulAut.conj : G →* MulAut G).range) (hS : IsSylowTwoOf S A) :
    Subgroup.normalizer (S : Set (MulAut G)) ⊓ A ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut G) :=
    Finite.of_injective (fun e : MulAut G => (e : G → G)) fun _ _ h => MulEquiv.ext (congrFun h)
  intro x hx
  obtain ⟨hxN, hxA⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  have hb : ((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m + (m : ℤ) * Nat.gcdB (2 ^ a) m = 1 := by
    have := Nat.gcd_eq_gcd_ab (2 ^ a) m
    rw [hcop.gcd_eq_one] at this
    exact_mod_cast this.symm
  have hxn : x ^ (2 ^ a * m) = 1 := hn ▸ pow_orderOf_eq_one x
  set y := (x ^ (2 ^ a)) ^ Nat.gcdA (2 ^ a) m with hy
  set z := (x ^ m) ^ Nat.gcdB (2 ^ a) m with hz
  have hxyz : x = y * z := by
    rw [hy, hz, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, hb, zpow_one]
  have hz2 : z ^ 2 ^ a = 1 := by
    rw [hz, KGHe.zpow_pow_comm', ← pow_mul, mul_comm, hxn, one_zpow]
  have hym : y ^ m = 1 := by
    rw [hy, KGHe.zpow_pow_comm', ← pow_mul, hxn, one_zpow]
  have hzS : z ∈ S := KGHe.mem_of_mem_normalizer_of_pow hS (A.zpow_mem (A.pow_mem hxA _) _)
    (Subgroup.zpow_mem _ (Subgroup.pow_mem _ hxN _) _) hz2
  have hyN : y ∈ Subgroup.normalizer (S : Set (MulAut G)) :=
    Subgroup.zpow_mem _ (Subgroup.pow_mem _ hxN _) _
  suffices hyS : y ∈ S by
    rw [hxyz]
    exact S.mul_mem hyS hzS
  have hSI : IsSylowTwoOf (S ⊓ inner G) (inner G) :=
    A4.isSylowTwoOf_inf_normal hS hA (fun g _ => Subgroup.mem_normalizer_iff.mpr fun h =>
      ⟨fun hh => (inner_normal G).conj_mem h hh g, fun hh => by
        have := (inner_normal G).conj_mem _ hh g⁻¹
        simpa [mul_assoc] using this⟩)
  have hNI : ∀ g ∈ Subgroup.normalizer (S : Set (MulAut G)),
      g ∈ Subgroup.normalizer ((S ⊓ inner G : Subgroup (MulAut G)) : Set (MulAut G)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.mp hg h]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (inner_normal G).conj_mem h h2 g⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := (inner_normal G).conj_mem _ h2 g⁻¹
      simpa [mul_assoc] using this
  let φ : G →* ↥(inner G) :=
    (MulAut.conj : G →* MulAut G).codRestrict (inner G) fun x => ⟨x, rfl⟩
  have hφ : ∀ g, (φ g : MulAut G) = MulAut.conj g := fun g => rfl
  let P : Subgroup G := ((S ⊓ inner G).subgroupOf (inner G)).comap φ
  have hmem : ∀ g : G, g ∈ P ↔ MulAut.conj g ∈ S ⊓ inner G := fun g => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hφ]
  have hφinj : Function.Injective φ := fun a b hab => hinj (by rw [← hφ a, ← hφ b, hab])
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, g, rfl⟩
    exact ⟨g, rfl⟩
  have hPsyl : IsSylowTwoOf P ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact (hSI.2.1.comap_of_injective (inner G).subtype Subtype.val_injective).comap_of_injective
        φ hφinj
    · have h1 : P.index = ((S ⊓ inner G).subgroupOf (inner G)).index :=
        Subgroup.index_comap_of_surjective _ hφsurj
      show ¬ 2 ∣ P.relIndex ⊤
      rw [Subgroup.relIndex_top_right, h1]
      exact hSI.2.2
  have hconj : ∀ (g : MulAut G) (x : G), MulAut.conj (g x) = g * MulAut.conj x * g⁻¹ := by
    intro g x
    ext y
    simp [MulAut.conj_apply, map_mul, map_inv]
  have hgP : ∀ g ∈ Subgroup.normalizer (S : Set (MulAut G)), ∀ x ∈ P, g x ∈ P := by
    intro g hg x hx
    rw [hmem] at hx ⊢
    rw [hconj]
    exact (Subgroup.mem_normalizer_iff.mp (hNI g hg) _).mp hx
  obtain ⟨hP4, hPsq⟩ := hsyl P hPsyl
  have hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    have h2 : a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left (hPsq _ (P.mul_mem ha hb))
    rw [h2, mul_inv_rev, inv_eq_of_mul_eq_one_left (hPsq b hb),
      inv_eq_of_mul_eq_one_left (hPsq a ha)]
  have hRtriv : ∀ r ∈ S ⊓ inner G, ∀ w ∈ P, r w = w := by
    intro r hr w hw
    obtain ⟨p, rfl⟩ := (Subgroup.mem_inf.mp hr).2
    have hp : p ∈ P := (hmem p).mpr hr
    rw [MulAut.conj_apply, hPcomm p hp w hw, mul_inv_cancel_right]
  set π : MulAut G →* Outer G := QuotientGroup.mk' (inner G) with hπ
  have hπker : ∀ g, π g = 1 ↔ g ∈ (inner G : Subgroup (MulAut G)) := fun g =>
    QuotientGroup.eq_one_iff g
  let H : Subgroup (Outer G) := S.map π
  have hHle : Nat.card H ≤ 2 :=
    Nat.le_of_dvd (by norm_num) ((Subgroup.card_subgroup_dvd_card H).trans hout)
  have huniq : ∀ u ∈ H, ∀ v ∈ H, u ≠ 1 → v ≠ 1 → u = v := by
    intro u hu v hv hu1 hv1
    have hnt : Nontrivial H := ⟨⟨1, ⟨u, hu⟩, fun h => hu1 (congrArg Subtype.val h).symm⟩⟩
    have h1 : 1 < Nat.card H := Finite.one_lt_card
    have h2 : Nat.card H = 2 := by omega
    obtain ⟨c, -, hc⟩ := (Nat.card_eq_two_iff' (1 : H)).mp h2
    have e1 := hc ⟨u, hu⟩ (fun h => hu1 (congrArg Subtype.val h))
    have e2 := hc ⟨v, hv⟩ (fun h => hv1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (e1.trans e2.symm)
  have hsqH : ∀ u ∈ H, u * u = 1 := by
    intro u hu
    by_contra h
    have hu1 : u ≠ 1 := fun h1 => h (by rw [h1, one_mul])
    have := huniq _ (H.mul_mem hu hu) _ hu h hu1
    exact hu1 (mul_left_cancel (this.trans (mul_one u).symm))
  have hinnA : inner G ≤ A := hA
  obtain ⟨t, htS, htI⟩ : ∃ t ∈ S, t ∉ (inner G : Subgroup (MulAut G)) := by
    by_contra hcon
    have hSI' : S ≤ inner G := fun s hs => by
      by_contra h
      exact hcon ⟨s, hs, h⟩
    let ρ : A →* Outer G := π.comp A.subtype
    have hker : ρ.ker = (inner G).subgroupOf A := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hπker g
    have hidx : (inner G).relIndex A ∣ 2 := by
      have h1 := Subgroup.index_ker ρ
      rw [hker] at h1
      show ((inner G).subgroupOf A).index ∣ 2
      rw [h1]
      exact (Subgroup.card_subgroup_dvd_card ρ.range).trans hout
    have hidx2 : (inner G).relIndex A = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h | h
      · exfalso
        apply hAne
        have h1 : (inner G).subgroupOf A = ⊤ := Subgroup.index_eq_one.mp h
        exact le_antisymm (fun g hg => by
          have : (⟨g, hg⟩ : A) ∈ (inner G).subgroupOf A := h1 ▸ Subgroup.mem_top _
          exact this) hA
      · exact h
    have hmul := Subgroup.relIndex_mul_relIndex S (inner G) A hSI' hinnA
    apply hS.2.2
    show 2 ∣ S.relIndex A
    rw [← hmul, hidx2]
    exact dvd_mul_left 2 _
  have htN : t ∈ Subgroup.normalizer (S : Set (MulAut G)) := Subgroup.le_normalizer htS
  have ht2 : t * t ∈ S ⊓ inner G :=
    Subgroup.mem_inf.mpr ⟨S.mul_mem htS htS, by
      rw [← hπker, map_mul]
      exact hsqH _ ⟨t, htS, rfl⟩⟩
  have hytS : y * t * y⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hyN t).mp htS
  have hytI : y * t * y⁻¹ ∉ (inner G : Subgroup (MulAut G)) := fun h => htI (by
    have := (inner_normal G).conj_mem _ h y⁻¹
    simpa [mul_assoc] using this)
  have heq : π t = π (y * t * y⁻¹) :=
    huniq _ ⟨t, htS, rfl⟩ _ ⟨_, hytS, rfl⟩ (fun h => htI ((hπker t).mp h))
      (fun h => hytI ((hπker _).mp h))
  obtain ⟨v₀, hv₀def⟩ : ∃ v₀, v₀ = t⁻¹ * (y * t * y⁻¹) := ⟨_, rfl⟩
  have hv₀ : v₀ ∈ S ⊓ inner G := hv₀def ▸
    Subgroup.mem_inf.mpr ⟨S.mul_mem (S.inv_mem htS) hytS, by
      rw [← hπker, map_mul, map_inv, ← heq, inv_mul_cancel]⟩
  have hyfix : ∀ w ∈ P, y w = w := by
    refine fix_of_comm_four hP4 hPsq t y (hgP t htN) (hgP y hyN) ?_ ?_ ?_ hm hym
    · intro w hw
      have := hRtriv _ ht2 w hw
      rwa [MulAut.mul_apply] at this
    · by_contra hcon
      have hall : ∀ w ∈ P, t w = w := fun w hw => by
        by_contra h
        exact hcon ⟨w, hw, h⟩
      obtain ⟨g, -, hg⟩ := hfix P hPsyl t hall
      exact htI ⟨g, hg.symm⟩
    · intro w hw
      have e : y * t = t * v₀ * y := by rw [hv₀def]; group
      have h1 : y (t w) = t (v₀ (y w)) := by
        rw [← MulAut.mul_apply, e, MulAut.mul_apply, MulAut.mul_apply]
      rw [h1, hRtriv _ hv₀ _ (hgP y hyN w hw)]
  obtain ⟨g, hgP', hg⟩ := hfix P hPsyl y hyfix
  rw [hg]
  exact (Subgroup.mem_inf.mp ((hmem g).mp hgP')).1

theorem isKleinFour_of_mulEquiv' {X Y : Type*} [Group X] [Group Y] [IsKleinFour Y] (e : X ≃* Y) :
    IsKleinFour X :=
  ⟨by rw [Nat.card_congr e.toEquiv]; exact IsKleinFour.card_four,
    by rw [Monoid.exponent_eq_of_mulEquiv e]; exact IsKleinFour.exponent_two⟩

open CFSG.GorensteinWalter (PSL2 IsOddPrimePower) in
theorem factAutL2pOuter_holds :
    FactAutL2pOuter := by
  intro p hp hp3 h8 Q _ _ hQ A S hA hAne hS
  have hQ' := hQ
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hK1 : Nat.card K = p := by rw [hK, pow_one]
  let e' : Q ≃* PSL2 K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hp5 : 5 ≤ p := by omega
  have hodd : IsOddPrimePower (Nat.card K) := ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, hK⟩
  have hZ : Subgroup.center Q = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    rw [Nat.card_congr (Subgroup.centerCongr e').toEquiv,
      CFSG.GorensteinWalter.psl2_center_eq_bot K, Subgroup.card_bot]
  have hsylD : ∀ P : Subgroup Q, IsSylowTwoOf P ⊤ → Nonempty (↥P ≃* DihedralGroup 2) := by
    intro P hP
    obtain ⟨hP2, hPi⟩ := K1.isSylowTwoOf_top_iff.mp hP
    let P' : Sylow 2 Q := hP2.toSylow hPi
    obtain ⟨T, hT⟩ := Sylow.exists_comap_eq_of_injective P' (f := e'.toMonoidHom) e'.injective
    have hTmap : (P : Subgroup Q).map e'.toMonoidHom = T := by
      rw [← IsPGroup.toSylow_coe hP2 hPi]
      show (P' : Subgroup Q).map e'.toMonoidHom = T
      rw [← hT]
      exact Subgroup.map_comap_eq_self_of_surjective e'.surjective _
    obtain ⟨m, -, ⟨eT⟩⟩ := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hodd T
    let iso : ↥P ≃* DihedralGroup (2 ^ m) :=
      ((e'.subgroupMap P).trans (MulEquiv.subgroupCongr hTmap)).trans eT
    have h4 : Nat.card P = 4 := factL2pSylowFour_holds p hp h8 Q hQ' P hP
    have hm : m = 1 := by
      have h1 := (Nat.card_congr iso.toEquiv).symm.trans h4
      rw [DihedralGroup.nat_card] at h1
      have : 2 ^ m = 2 ^ 1 := by omega
      exact Nat.pow_right_injective le_rfl this
    subst hm
    exact ⟨iso⟩
  have hsyl : ∀ P : Subgroup Q, IsSylowTwoOf P ⊤ → Nat.card P = 4 ∧ ∀ z ∈ P, z * z = 1 := by
    intro P hP
    obtain ⟨iso⟩ := hsylD P hP
    refine ⟨by rw [Nat.card_congr iso.toEquiv]; exact IsKleinFour.card_four, fun z hz => ?_⟩
    have h1 : ∀ d : DihedralGroup 2, d * d = 1 := by decide
    have h2 := h1 (iso ⟨z, hz⟩)
    rw [← map_mul, ← map_one iso] at h2
    exact congrArg Subtype.val (iso.injective h2)
  have hfix : ∀ P : Subgroup Q, IsSylowTwoOf P ⊤ → ∀ α : MulAut Q, (∀ z ∈ P, α z = z) →
      ∃ g ∈ P, α = MulAut.conj g := by
    intro P hP α hα
    obtain ⟨iso⟩ := hsylD P hP
    let V : Subgroup (PSL2 K) := P.map e'.toMonoidHom
    have hV : IsKleinFour V := isKleinFour_of_mulEquiv' ((e'.subgroupMap P).symm.trans iso)
    let α' : MulAut (PSL2 K) := (e'.symm.trans α).trans e'
    have hα' : ∀ v ∈ V, α' v = v := by
      rintro _ ⟨z, hz, rfl⟩
      show e' (α (e'.symm (e' z))) = e' z
      rw [MulEquiv.symm_apply_apply, hα z hz]
    obtain ⟨g0, hg0, hα'g⟩ := KG68.psl2_aut_fix_four_prime hp hp5 hK1 hV hα'
    obtain ⟨z0, hz0, rfl⟩ := hg0
    refine ⟨z0, hz0, MulEquiv.ext fun x => ?_⟩
    have h1 := congrArg (fun β : MulAut (PSL2 K) => β (e' x)) hα'g
    simp only [MulAut.conj_apply] at h1
    have h2 : α x = e'.symm (α' (e' x)) := by
      show α x = e'.symm (e' (α (e'.symm (e' x))))
      rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    rw [h2, h1, MulAut.conj_apply]
    simp
  have hout : Nat.card (Outer Q) ∣ 2 := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor hp K hK).2 Q
      ⟨e'⟩
    exact h.trans (by rw [one_mul]; exact Nat.gcd_dvd_left 2 _)
  exact normalizer_inf_le_of_four (KG68.conj_injective_of_center hZ) hsyl hfix hout hA hAne hS

end CFSG.Quasithin.H13.KGAutSyl
