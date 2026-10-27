module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section UnitaryRank

section Helpers

open CFSG.Assembly TableB CFSG.RankThree.Classical2 CFSG.RankThree.Classical
  CFSG.SectionRank.OddCover CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open TableBU
open CFSG.LieType.Steinberg

private theorem exists_lift_of_section_noU {H R L : Type} [Group H] [Group R] [Group L]
    [Finite H] [Finite L] (q : H →* R)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : H →* E, ∀ h, π (s h) = h)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E₀ : Subgroup H} (hE₀ : IsElemAbelian p E₀)
    (hE₀q : E₀ ⊓ q.ker = ⊥) (ψ : L →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) :
    ∃ E : Subgroup L, IsElemAbelian p E ∧ Nat.card E = Nat.card E₀ ∧ E ⊓ ψ.ker = ⊥ := by
  classical
  have := Fact.mk hp
  set N := twoPartOf ψ.ker hker (Nat.card L) with hNdef
  have hNk : N ≤ ψ.ker := twoPartOf_le _ hker _
  set π : L →* L ⧸ N := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hkerπ : π.ker = N := QuotientGroup.ker_mk' N
  set ψb : L ⧸ N →* R := QuotientGroup.lift N ψ hNk with hψb
  have hψbπ : ∀ l, ψb (π l) = ψ l := fun l => QuotientGroup.lift_mk N hNk l
  have hψbs : Function.Surjective ψb := by
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    exact ⟨π l, hψbπ l⟩
  have hψbc : ψb.ker ≤ Subgroup.center (L ⧸ N) := by
    intro y hy
    obtain ⟨z, rfl⟩ := hπs y
    have hz : z ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hψbπ]
      exact hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨v, rfl⟩ := hπs w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hker hz) v]
  have hψbodd : ∀ y ∈ ψb.ker, y ^ 2 = 1 → y = 1 := fun y hy hy2 =>
    sq_eq_one_ker_lift hker y hy hy2
  set Pb := pullback q ψb with hPb
  have hfst := pullbackFst_surjective (β := q) hψbs
  have hfstc := ker_pullbackFst_le_center (β := q) hψbc
  have hcop : Nat.Coprime 2 (Nat.card (pullbackFst q ψb).ker) := by
    refine coprime_two_card_of_sq fun y hy2 => ?_
    obtain ⟨h1, h2⟩ := snd_mem_ker_of_mem_ker_pullbackFst y.2
    have h3 : (((y : Pb) : H × (L ⧸ N)).2) ^ 2 = 1 := by
      have := congrArg (fun z : (pullbackFst q ψb).ker => ((z : Pb) : H × (L ⧸ N)).2) hy2
      simpa using this
    have h4 := hψbodd _ h2 h3
    exact Subtype.ext (Subtype.ext (Prod.ext h1 h4))
  obtain ⟨σ, hσ⟩ := hsplit Pb (pullbackFst q ψb) hfst hfstc hcop
  set α : H →* L ⧸ N := ((MonoidHom.snd H (L ⧸ N)).comp Pb.subtype).comp σ with hαdef
  have hα : ∀ h, ψb (α h) = q h := by
    intro h
    have hmem := mem_pullback.1 (σ h).2
    have h1 : ((σ h : Pb) : H × (L ⧸ N)).1 = h := hσ h
    change ψb ((σ h : Pb) : H × (L ⧸ N)).2 = q h
    rw [← hmem, h1]
  set E' := E₀.map α with hE'
  have hinj : Function.Injective (α.comp E₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : q (a : H) = 1 := by
      rw [← hα, show α (a : H) = 1 from ha, map_one]
    have h2 : (a : H) ∈ E₀ ⊓ q.ker := ⟨a.2, h1⟩
    rw [hE₀q, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hE'card : Nat.card E' = Nat.card E₀ := by
    have h1 : (α.comp E₀.subtype).range = E' := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hE'ab : IsElemAbelian p E' := isElemAbelian_map hE₀ α
  set H' := E'.comap π with hH'
  have hNH' : N ≤ H' := by
    intro n hn
    have hn' : n ∈ π.ker := by
      rw [hkerπ]
      exact hn
    show π n ∈ E'
    rw [show π n = 1 from hn']
    exact E'.one_mem
  set f' : H' →* L ⧸ N := π.comp H'.subtype with hf'
  have hkerf' : f'.ker = N.subgroupOf H' := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show π h = 1 ↔ (h : L) ∈ N
    rw [← MonoidHom.mem_ker, hkerπ]
  have hrangef' : f'.range = E' := by
    ext y
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨h, rfl⟩
      exact h.2
    · intro hy
      obtain ⟨l, rfl⟩ := hπs y
      exact ⟨⟨l, hy⟩, rfl⟩
  have hindex : (N.subgroupOf H').index = Nat.card E₀ := by
    rw [← hkerf', Subgroup.index_ker, hrangef', hE'card]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (isPGroup_twoPartOf ψ.ker hker (Nat.card L))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hE₀)
  have hcardN' : Nat.card (N.subgroupOf H') = 2 ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH').toEquiv]
    exact ha
  have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr fun h => hp2 h.symm
  have hcop' : Nat.Coprime (Nat.card (N.subgroupOf H')) (N.subgroupOf H').index := by
    rw [hcardN', hindex, hm]
    exact Nat.Coprime.pow a m h2p
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime hcop'
  have hCcard : Nat.card C = Nat.card E₀ := by
    have h1 := hC.card_mul_card
    have h2 := Subgroup.card_mul_index (N.subgroupOf H')
    rw [← hindex]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  set E : Subgroup L := C.map H'.subtype with hEdef
  have hEN : ∀ e ∈ E, π e = 1 → e = 1 := by
    rintro _ ⟨c, hc, rfl⟩ hce
    have hcN : c ∈ N.subgroupOf H' := by
      rw [← hkerf']
      exact hce
    have hc1 : c ∈ N.subgroupOf H' ⊓ C := ⟨hcN, hc⟩
    rw [hC.disjoint.eq_bot, Subgroup.mem_bot] at hc1
    rw [hc1]
    rfl
  have hEE' : ∀ e ∈ E, π e ∈ E' := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun e he => ?_⟩
    · have hc : (x : L) * y * (x : L)⁻¹ * (y : L)⁻¹ = 1 := by
        refine hEN _ (E.mul_mem (E.mul_mem (E.mul_mem x.2 y.2) (E.inv_mem x.2)) (E.inv_mem y.2)) ?_
        have hxy := IsElemAbelian.comm hE'ab (hEE' _ x.2) (hEE' _ y.2)
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxy]
        group
      show (x : L) * y = y * x
      calc (x : L) * y = (x : L) * y * (x : L)⁻¹ * (y : L)⁻¹ * (y * x) := by group
        _ = y * x := by rw [hc, one_mul]
    · refine hEN _ (E.pow_mem he p) ?_
      rw [map_pow]
      exact hE'ab.2 _ (hEE' e he)
  have hEcard : Nat.card E = Nat.card E₀ := by
    rw [hEdef, Subgroup.card_map_of_injective H'.subtype_injective, hCcard]
  have hEker : E ⊓ ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨heE, heK⟩
    obtain ⟨s, hs, hse⟩ := hEE' e heE
    have hqs : q s = 1 := by
      rw [← hα, hse, hψbπ]
      exact heK
    have hs1 : s ∈ E₀ ⊓ q.ker := ⟨hs, hqs⟩
    rw [hE₀q, Subgroup.mem_bot] at hs1
    rw [hs1, map_one] at hse
    exact (Subgroup.mem_bot).mpr (hEN e heE hse.symm)
  exact ⟨E, hEab, hEcard, hEker⟩

private noncomputable def pThreeTorusGen {K : Type} [Field K] {d : ℕ} (hd4 : 4 < d) (ζ : Kˣ)
    (j : Fin 4) : Fin d → Kˣ :=
  (Pi.mulSingle (⟨j, by omega⟩ : Fin d) ζ : Fin d → Kˣ) *
    (Pi.mulSingle (⟨4, hd4⟩ : Fin d) ζ⁻¹ : Fin d → Kˣ)

private theorem pThreeTorusGen_apply {K : Type} [Field K] {d : ℕ} (hd4 : 4 < d) (ζ : Kˣ)
    (j : Fin 4) (i : Fin d) :
    pThreeTorusGen hd4 ζ j i =
      (if (i : ℕ) = (j : ℕ) then ζ else 1) * (if (i : ℕ) = 4 then ζ⁻¹ else 1) := by
  simp only [pThreeTorusGen, Pi.mul_apply, Pi.mulSingle_apply, Fin.ext_iff]

private theorem pThreeTorusGen_pow {K : Type} [Field K] {d : ℕ} {ζ : Kˣ} {k : ℕ}
    (hζ : ζ ^ k = 1) (hd4 : 4 < d) (j : Fin 4) (i : Fin d) :
    pThreeTorusGen hd4 ζ j i ^ k = 1 := by
  rw [pThreeTorusGen_apply, mul_pow]
  have h3 : (ζ⁻¹) ^ k = 1 := by rw [inv_pow, hζ, inv_one]
  split_ifs <;> simp [hζ, h3]

private theorem pThreeTorusGen_prod {K : Type} [Field K] {d : ℕ} (hd4 : 4 < d) (ζ : Kˣ)
    (j : Fin 4) : ∏ i, pThreeTorusGen hd4 ζ j i = 1 := by
  simp only [pThreeTorusGen, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
  group

private theorem pThreeTorusGen_eq_one {K : Type} [Field K] {d : ℕ} (hd4 : 4 < d) (ζ : Kˣ)
    {i : Fin d} {j : Fin 4} (hij : (i : ℕ) ≠ (j : ℕ)) (hi4 : (i : ℕ) ≠ 4) :
    pThreeTorusGen hd4 ζ j i = 1 := by
  rw [pThreeTorusGen_apply]
  simp [hij, hi4]

private theorem pThreeTorusGen_orderOf {K : Type} [Field K] {d : ℕ} (hd4 : 4 < d) {ζ : Kˣ}
    (hζo : orderOf ζ = 3) (j : Fin 4) :
    orderOf (pThreeTorusGen hd4 ζ j ⟨j, by omega⟩) = 3 := by
  rw [pThreeTorusGen_apply]
  have h2 : ¬ ((j : ℕ) = 4) := by omega
  simp [h2, hζo]

private theorem exists_elemAbelian_pThree_unitarySU {K : Type} [Field K] [Finite K] {n d : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : d = 5 ∨ d = 6)
    (hpq : 3 ∣ 2 ^ n + 1) :
    ∃ E₀ : Subgroup (LargeEvenSUGroup (Fin d) K (2 ^ n)),
      IsElemAbelian 3 E₀ ∧ Nat.card E₀ = 3 ^ 4 ∧
        E₀ ⊓ (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))).ker = ⊥ := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have : NeZero 3 := ⟨hp.ne_zero⟩
  have hKd : UnitaryFieldData 2 n K := unitaryFieldData_of_card hK hn
  have hd4 : 4 < d := by rcases hd with h | h <;> omega
  set H := LargeEvenSUGroup (Fin d) K (2 ^ n) with hH
  obtain ⟨ζ, hζo, hζq⟩ := exists_orderOf_eq_norm_one hKd hp hpq
  have hζ3 : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  let c : Fin 4 → Fin d → Kˣ := pThreeTorusGen hd4 ζ
  have hcp : ∀ j i, c j i ^ 3 = 1 := fun j i => pThreeTorusGen_pow hζ3 hd4 j i
  have hcprod : ∀ j, ∏ i, c j i = 1 := fun j => pThreeTorusGen_prod hd4 ζ j
  have hcnorm : ∀ j i, c j i ^ (2 ^ n + 1) = 1 := fun j i => pThreeTorusGen_pow hζq hd4 j i
  have hmemH : ∀ a, diagHom d (expHom c hcp a) ∈ H := fun a =>
    diagHom_expHom_mem_unitarySU hKd c hcp hcprod hcnorm a
  have hpriv : ∀ j, ∃ i, (∀ j', j' ≠ j → c j' i = 1) ∧ orderOf (c j i) = 3 := by
    intro j
    refine ⟨⟨j, by omega⟩, fun j' hj' => ?_, ?_⟩
    · show pThreeTorusGen hd4 ζ j' ⟨j, by omega⟩ = 1
      exact pThreeTorusGen_eq_one hd4 ζ (fun h => hj' (Fin.ext h.symm)) (Nat.ne_of_lt j.isLt)
    · show orderOf (pThreeTorusGen hd4 ζ j ⟨j, by omega⟩) = 3
      exact pThreeTorusGen_orderOf hd4 hζo j
  have hexpinj := expHom_injective c hcp hpriv
  set φ : Multiplicative (Fin 4 → ZMod 3) →* H :=
    ((diagHom d).comp (expHom c hcp)).codRestrict H hmemH with hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : diagHom d (expHom c hcp a) = diagHom d (expHom c hcp b) := congrArg Subtype.val hab
    exact hexpinj (diagHom_injective d h1)
  set E₀ := φ.range with hE₀
  have hE₀card : Nat.card E₀ = 3 ^ 4 := by
    rw [hE₀, Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hapow : ∀ a : Multiplicative (Fin 4 → ZMod 3), a ^ 3 = 1 := by
    intro a
    rw [← toAdd_eq_zero, toAdd_pow]
    funext i
    simp only [Pi.smul_apply, nsmul_eq_mul]
    rw [ZMod.natCast_self, zero_mul]
    rfl
  have hE₀ab : IsElemAbelian 3 E₀ := isElemAbelian_range (fun a b => mul_comm a b) hapow φ
  set q := LargeEvenProjMk H with hq
  have hkerq : q.ker = (LargeEvenScalars (Fin d) K).subgroupOf H := QuotientGroup.ker_mk' _
  have hscal : ∀ x : H, x ∈ q.ker → (x : GL (Fin d) K) ∈ Subgroup.center (GL (Fin d) K) := by
    intro x hx
    rw [hkerq, Subgroup.mem_subgroupOf] at hx
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hx
  have hE₀q : E₀ ⊓ q.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨a, rfl⟩, hx⟩
    have hcen : diagHom d (expHom c hcp a) ∈ Subgroup.center (GL (Fin d) K) := hscal _ hx
    have htc := diagHom_eq_of_mem_center hcen
    have htp : ∀ i, expHom c hcp a i ^ 3 = 1 := by
      intro i
      have h1 : expHom c hcp a ^ 3 = 1 := by rw [← map_pow, hapow, map_one]
      exact congrFun h1 i
    have ht1 : expHom c hcp a = 1 := by
      have hlast : ∃ u, u = 1 ∧ ∀ i, expHom c hcp a i = u := by
        by_cases h3d : 3 ∣ d
        ·
          have hd6 : d = 6 := by
            rcases hd with h | h
            · subst h; norm_num at h3d
            · exact h
          have h5d : (5 : ℕ) < d := by omega
          refine ⟨expHom c hcp a ⟨5, h5d⟩, ?_, fun i => htc _ _⟩
          rw [expHom_apply]
          refine Finset.prod_eq_one fun j _ => ?_
          have hj1 : c j ⟨5, h5d⟩ = 1 := by
            show pThreeTorusGen hd4 ζ j ⟨5, h5d⟩ = 1
            have hj5 : (j : ℕ) < 5 := Nat.lt_trans j.isLt (by norm_num)
            exact pThreeTorusGen_eq_one (i := ⟨5, h5d⟩) (j := j) hd4 ζ
              (Ne.symm (Nat.ne_of_lt hj5)) (by norm_num)
          rw [hj1, one_pow]
        ·
          refine ⟨expHom c hcp a ⟨0, by omega⟩, ?_, fun i => htc _ _⟩
          set u := expHom c hcp a ⟨0, by omega⟩ with hu
          have hdet := ((mem_unitarySU_iff hKd).mp (hmemH a)).1
          rw [det_diagHom] at hdet
          have hud : u ^ d = 1 := by
            apply Units.ext
            rw [Units.val_pow_eq_pow_val, Units.val_one, ← hdet]
            rw [Finset.prod_congr rfl fun i _ => congrArg Units.val (htc i ⟨0, by omega⟩),
              Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          have hcop : Nat.gcd d 3 = 1 :=
            Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr h3d)
          have h1 := pow_gcd_eq_one.mpr ⟨hud, htp ⟨0, by omega⟩⟩
          rwa [hcop, pow_one] at h1
      obtain ⟨u, hu1, hu⟩ := hlast
      funext i
      rw [hu i, hu1]
      rfl
    have ha1 : a = 1 := hexpinj (by rw [ht1, map_one])
    rw [ha1, map_one]
    exact Subgroup.one_mem _
  exact ⟨E₀, hE₀ab, hE₀card, hE₀q⟩

private theorem unitarySU_split_section
    {K : Type} [Field K] [Finite K]
    {n d : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : d = 5 ∨ d = 6) :
    ∀ (E : Type) [Group E] [Finite E] (π : E →* LargeEvenSUGroup (Fin d) K (2 ^ n)),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : LargeEvenSUGroup (Fin d) K (2 ^ n) →* E, ∀ h, π (s h) = h := by
  have hKd : UnitaryFieldData 2 n K := unitaryFieldData_of_card hK hn
  have : CharP K 2 := hKd.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd3 : 3 ≤ d := by rcases hd with h | h <;> omega
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    rintro h
    have h1 : d = 3 := congrArg Prod.fst h
    rcases hd with h5 | h6 <;> omega
  intro E _ _ π hπ hcen hC
  by_cases he : Even d
  · exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_coprime
      (F := K) (p := 2) (f := n) hK he (by omega) E π hπ hcen hC
  · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
      (F := K) (p := 2) (f := n) hK hn hd3 he hdq hπ hcen

end Helpers

theorem ggTablePThree_unitaryThreeRank
    {X : Type} [Group X] [Finite X]
    (hM : LargeEvenMarking X fun lab _ _ _ _ _ =>
      lab.tag = .twA ∧ (lab.rank = 4 ∨ lab.rank = 5) ∧ 3 ∣ 2 ^ lab.n + 1) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ E ⊓ Subgroup.center X = ⊥ := by
  classical
  obtain ⟨-, lab, hlab, hraw⟩ := hM
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨R₀, iR₀, I₀, F₀, hs₀, hna₀, θ₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  dsimp only at hP₀
  have htag : t = .twA := hP₀.1
  subst htag
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, iK, iKf, hK, hs, hna, θ, hθP⟩ := hraw
  have hn : 1 ≤ n := hlab.1
  have hrank : l = 4 ∨ l = 5 := hθP.2.1
  have hpq : 3 ∣ 2 ^ n + 1 := hθP.2.2
  set d : ℕ := l + 1 with hd_def
  have hd : d = 5 ∨ d = 6 := by
    rw [hd_def]
    rcases hrank with h | h <;> omega
  obtain ⟨E₀, hE₀ab, hE₀card, hE₀q⟩ :=
    exists_elemAbelian_pThree_unitarySU (K := K) (n := n) (d := d) hK hn hd hpq
  have hsplit := unitarySU_split_section (K := K) (n := n) (d := d) hK hn hd
  let ψ : X →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψ : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    change θ (QuotientGroup.mk x) = 1 ↔ x ∈ Subgroup.center X
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  obtain ⟨E, hEab, hEcard, hEker⟩ :=
    exists_lift_of_section_noU (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      hsplit Nat.prime_three (by norm_num) hE₀ab hE₀q ψ hψ hker.le
  exact ⟨E, hEab, hEcard.trans hE₀card, by rw [hker] at hEker; exact hEker⟩

end UnitaryRank

end CFSG.StandardType
