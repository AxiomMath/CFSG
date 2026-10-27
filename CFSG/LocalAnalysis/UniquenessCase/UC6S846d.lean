module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10
public import CFSG.LocalAnalysis.UniquenessCase.UCKU3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S846

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem three_dvd_two_pow_add_one {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h : 4 ^ k ≡ 1 [MOD 3] := by
    simpa using (Nat.ModEq.pow k (show 4 ≡ 1 [MOD 3] by decide))
  have h2 : 2 ^ (2 * k + 1) + 1 = 2 * 4 ^ k + 1 := by
    rw [pow_succ, pow_mul]; norm_num; ring
  rw [h2]
  have h3 := Nat.ModEq.add_right 1 (Nat.ModEq.mul_left 2 h)
  exact (Nat.modEq_zero_iff_dvd).1 (h3.trans (by decide))

theorem lift_maximal {H K : Type*} [Group H] [Group K] [Finite H] (f : H →* K) {q : ℕ}
    (SL : Subgroup H) (S : Subgroup K) (hmap : SL.map f = S) (hdisj : Disjoint SL f.ker)
    (hker : IsPGroup 2 f.ker) (hq : q.Prime) (hq2 : q ≠ 2)
    (hmax : ∀ T : Subgroup K, IsPGroup q T → S ≤ T → T = S) (hSL : IsPGroup q SL) :
    ∀ T : Subgroup H, IsPGroup q T → SL ≤ T → T = SL := by
  intro T hT hSLT
  have hTdisj : Disjoint T f.ker := by
    rw [Subgroup.disjoint_def]
    intro x hxT hxker
    obtain ⟨a, ha⟩ := hT ⟨x, hxT⟩
    obtain ⟨b, hb⟩ := hker ⟨x, hxker⟩
    have ha' : x ^ q ^ a = 1 := by simpa using ha
    have hb' : x ^ 2 ^ b = 1 := by simpa using hb
    have hcop : Nat.Coprime (q ^ a) (2 ^ b) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
    have h1 : orderOf x ∣ Nat.gcd (q ^ a) (2 ^ b) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha') (orderOf_dvd_of_pow_eq_one hb')
    rw [hcop.gcd_eq_one] at h1
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  have hTq : IsPGroup q (T.map f) := hT.map f
  have hST : S ≤ T.map f := hmap ▸ Subgroup.map_mono hSLT
  have hTS : T.map f = S := hmax _ hTq hST
  have hcard : Nat.card T = Nat.card SL := by
    rw [← card_map_of_disjoint_ker f T hTdisj, ← card_map_of_disjoint_ker f SL hdisj, hTS, hmap]
  exact (Subgroup.eq_of_le_of_card_ge hSLT (by rw [hcard])).symm

theorem keyLemma (hOut : UCK.U3OutShape) (hKey : UCK.U3Key) {M L : Subgroup G} (hLM : L ≤ M)
    (hN : M ≤ normalizer (L : Set G)) {n : ℕ} (hX : IsSU3 (Bar2 L) n) {q p : ℕ} (hq : q.Prime)
    (hq3 : 3 < q) (hqn : q ∣ 2 ^ n + 1) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q)
    (hOp : UC22.F10.OpRes p M = M) (hrank : 3 ≤ Open.pRank p M) :
    ∃ S E A : Subgroup G, S ≤ L ∧ IsPGroup q S ∧
      (∀ T : Subgroup G, T ≤ L → IsPGroup q T → S ≤ T → T = S) ∧
      E ≤ S ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 2 ∧
      A ≤ M ∧ A ≤ centralizer (E : Set G) ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
      ∃ Sb : Subgroup (Bar2 L), IsPGroup q Sb ∧ ¬ q ∣ Sb.index ∧
        (S.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = Sb := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hq2 : q ≠ 2 := by rintro rfl; omega
  set N : Subgroup G := normalizer (L : Set G) with hNdef
  set O : Subgroup G := pCoreOf 2 L with hOdef
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hNO : N ≤ normalizer (O : Set G) := normalizer_le_normalizer_pCoreOf L
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hMN : M ≤ N := hN
  have hOpg : IsPGroup 2 O := isPGroup_pCoreOf L
  have hOL : O ≤ L := Subgroup.map_subtype_le _
  obtain ⟨A₀, hA₀M, hA₀el, hA₀card⟩ := exists_elemAbelian_card_of_le_pRank hp hrank
  let ρ : ↥N →* MulAut (Bar2 L) := rhoL L
  let A₀N : Subgroup ↥N := A₀.subgroupOf N
  have hA₀N : A₀ ≤ N := hA₀M.trans hMN
  have hA₀Nel : IsElemAbelian p A₀N := hA₀el.subgroupOf N
  let R : Subgroup (MulAut (Bar2 L)) := A₀N.map ρ
  have hRel : IsElemAbelian p R := hA₀Nel.map ρ
  have hSC : R ≤ (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range ∨ p ∣ 2 ^ n + 1 := by
    by_cases hpd : p ∣ 2 ^ n + 1
    · exact Or.inr hpd
    left
    obtain ⟨Nsub, hNn, hInn, hcyc, hcube, hEven⟩ := hOut (Bar2 L) n hX
    haveI := hNn
    let MN : Subgroup ↥N := M.subgroupOf N
    let H : Subgroup (MulAut (Bar2 L)) := MN.map ρ
    have hgenMN := closure_pPrime_subgroupOf hMN (p := p) hOp
    have hgen := closure_pPrime_map ρ MN hgenMN
    have hp3 : p ≠ 3 ∨ Nsub ≤ (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range := by
      by_cases h3 : p = 3
      · right
        apply hEven
        rcases Nat.even_or_odd n with h | h
        · exact h
        · exfalso; exact hpd (h3 ▸ three_dvd_two_pow_add_one h)
      · left; exact h3
    intro r hr
    obtain ⟨a, ha, rfl⟩ := hr
    have haA : (a : G) ∈ A₀ := ha
    have hap : ρ a ^ (p ^ 1) = 1 := by
      rw [← map_pow]
      have : a ^ p ^ 1 = 1 := Subtype.ext (by simpa using hA₀el.2 _ haA)
      rw [this, map_one]
    exact mem_inner_of_pPow _ Nsub H hcyc hcube hp hp3 hgen
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (hA₀M haA))) hap
  obtain ⟨S, hSp, hSidx, E₀, hE₀S, hE₀el, hE₀card, hdisj⟩ :=
    hKey (Bar2 L) n hX q p hq hq3 hqn hp hp2 hpq R hRel hSC
  obtain ⟨SL, hSLp, hSLmap, hSLdisj⟩ := exists_lift_pGroup π hπsurj hker hq hq2 S hSp
  have hSmax : ∀ T : Subgroup (Bar2 L), IsPGroup q T → S ≤ T → T = S := by
    intro T hT hST
    have := (hSp.toSylow hSidx).is_maximal' hT (by simpa using hST)
    simpa using this
  have hSLmax := lift_maximal π SL S hSLmap hSLdisj hker hq hq2 hSmax hSLp
  let E' : Subgroup ↥L := SL ⊓ E₀.comap π
  have hE'map : E'.map π = E₀ := by
    ext y
    constructor
    · rintro ⟨x, ⟨_, hx2⟩, rfl⟩
      exact hx2
    · intro hy
      have hyS : y ∈ SL.map π := by rw [hSLmap]; exact hE₀S hy
      obtain ⟨x, hxS, rfl⟩ := hyS
      exact ⟨x, ⟨hxS, hy⟩, rfl⟩
  have hE'disj : Disjoint E' π.ker := hSLdisj.mono_left inf_le_left
  have hE'card : Nat.card E' = q ^ 2 := by
    rw [← card_map_of_disjoint_ker π E' hE'disj, hE'map, hE₀card]
  have hE'el : IsElemAbelian q E' :=
    isElemAbelian_of_disjoint_ker π E' hE'disj (by rw [hE'map]; exact hE₀el)
  let SG : Subgroup G := SL.map L.subtype
  let EG : Subgroup G := E'.map L.subtype
  have hSGL : SG ≤ L := Subgroup.map_subtype_le _
  have hEGS : EG ≤ SG := Subgroup.map_mono inf_le_left
  have hSGp : IsPGroup q SG := hSLp.map L.subtype
  have hEGcard : Nat.card EG = q ^ 2 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hE'card]
  have hEGel : IsElemAbelian q EG := hE'el.map L.subtype
  have hSGmax : ∀ T : Subgroup G, T ≤ L → IsPGroup q T → SG ≤ T → T = SG := by
    intro T hTL hT hST
    have hT' : IsPGroup q (T.subgroupOf L) :=
      hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
    have hSLT : SL ≤ T.subgroupOf L := by
      intro x hx
      exact hST ⟨x, hx, rfl⟩
    have h1 := hSLmax _ hT' hSLT
    calc T = (T.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hTL).symm
      _ = SL.map L.subtype := by rw [h1]
  have hELO : EG ≤ normalizer (O : Set G) := (hEGS.trans hSGL).trans (hLN.trans hNO)
  obtain ⟨A₂, hA₂M, hA₂el, hA₂card, hA₂comm⟩ : ∃ A₂ : Subgroup G, A₂ ≤ M ∧ IsElemAbelian p A₂ ∧
      Nat.card A₂ = p ^ 2 ∧ ∀ e ∈ EG, ∀ a ∈ A₂, e * a * e⁻¹ * a⁻¹ ∈ O := by
    rcases hdisj with ⟨B, hBel, hBcard, hBc⟩ | ⟨C, hCR, hCfix, hCcard⟩
    · obtain ⟨BL, hBLp, hBLmap, hBLdisj⟩ :=
        exists_lift_pGroup π hπsurj hker hp hp2 B hBel.isPGroup
      refine ⟨BL.map L.subtype, (Subgroup.map_subtype_le _).trans hLM, ?_, ?_, ?_⟩
      · exact (isElemAbelian_of_disjoint_ker π BL hBLdisj (by rw [hBLmap]; exact hBel)).map _
      · rw [Subgroup.card_map_of_injective L.subtype_injective,
          ← card_map_of_disjoint_ker π BL hBLdisj, hBLmap, hBcard]
      · rintro e ⟨e', he', rfl⟩ a ⟨b', hb', rfl⟩
        have h1 : π e' ∈ E₀ := by rw [← hE'map]; exact ⟨e', he', rfl⟩
        have h2 : π b' ∈ B := by rw [← hBLmap]; exact ⟨b', hb', rfl⟩
        have h3 : π b' ∈ centralizer (E₀ : Set (Bar2 L)) := hBc h2
        have h4 : π e' * π b' = π b' * π e' := Subgroup.mem_centralizer_iff.1 h3 _ h1
        have h5 : e' * b' * e'⁻¹ * b'⁻¹ ∈ π.ker := by
          rw [MonoidHom.mem_ker]
          simp only [map_mul, map_inv]
          rw [h4]
          group
        have h6 : e' * b' * e'⁻¹ * b'⁻¹ ∈ CFSG.pCore 2 ↥L := by
          rwa [show π.ker = CFSG.pCore 2 ↥L from QuotientGroup.ker_mk' _] at h5
        exact ⟨_, h6, by simp⟩
    · let φ : ↥A₀N →* MulAut (Bar2 L) := ρ.comp A₀N.subtype
      have hφrange : φ.range = R := by
        ext y
        simp only [φ, R, MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.comp_apply,
          Subgroup.coe_subtype]
        constructor
        · rintro ⟨a, rfl⟩; exact ⟨a, a.2, rfl⟩
        · rintro ⟨a, ha, rfl⟩; exact ⟨⟨a, ha⟩, rfl⟩
      let f : ↥A₀N →* ↥φ.range := φ.rangeRestrict
      have hfsurj : Function.Surjective f := φ.rangeRestrict_surjective
      have hCle : C ≤ φ.range := hφrange ▸ hCR
      let C' : Subgroup ↥φ.range := C.subgroupOf φ.range
      have hC'card : Nat.card C' = Nat.card C :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCle).toEquiv
      have hRcard : Nat.card φ.range = Nat.card R := by rw [hφrange]
      have hidx : C'.index ≤ p := by
        have h1 : Nat.card C' * C'.index = Nat.card φ.range := Subgroup.card_mul_index C'
        rw [hC'card, hRcard] at h1
        have hCpos : 0 < Nat.card C := Nat.card_pos
        by_contra hlt
        replace hlt := not_le.1 hlt
        have h2 : Nat.card C * (p + 1) ≤ Nat.card C * C'.index := Nat.mul_le_mul_left _ hlt
        nlinarith [hCcard, h1, h2, hCpos]
      let Cn : Subgroup ↥A₀N := C'.comap f
      have hCnidx : Cn.index = C'.index := Subgroup.index_comap_of_surjective C' hfsurj
      have hA₀Ncard : Nat.card A₀N = p ^ 3 := by
        rw [← hA₀card]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀N).toEquiv
      have hCncard : p ^ 2 ≤ Nat.card Cn := by
        have h1 : Nat.card Cn * Cn.index = Nat.card A₀N := Subgroup.card_mul_index Cn
        rw [hCnidx, hA₀Ncard] at h1
        by_contra hlt
        replace hlt := not_le.1 hlt
        have h2 : Nat.card Cn * C'.index ≤ Nat.card Cn * p := Nat.mul_le_mul_left _ hidx
        have h3 : Nat.card Cn * p < p ^ 2 * p := Nat.mul_lt_mul_of_pos_right hlt hp.pos
        have h4 : p ^ 3 < p ^ 3 :=
          calc p ^ 3 = Nat.card Cn * C'.index := h1.symm
            _ ≤ Nat.card Cn * p := h2
            _ < p ^ 2 * p := h3
            _ = p ^ 3 := by ring
        exact lt_irrefl _ h4
      let AE : Subgroup G := (Cn.map A₀N.subtype).map N.subtype
      have hAEcard : Nat.card AE = Nat.card Cn := by
        rw [Subgroup.card_map_of_injective N.subtype_injective,
          Subgroup.card_map_of_injective A₀N.subtype_injective]
      have hAEle : AE ≤ A₀ :=
        calc AE ≤ A₀N.map N.subtype := Subgroup.map_mono (Subgroup.map_subtype_le Cn)
          _ = A₀ := Subgroup.map_subgroupOf_eq_of_le hA₀N
      obtain ⟨A₂, hA₂AE, hA₂el, hA₂card⟩ :=
        exists_card_p_sq hp (hA₀el.mono hAEle) (by rw [hAEcard]; exact hCncard)
      refine ⟨A₂, hA₂AE.trans (hAEle.trans hA₀M), hA₂el, hA₂card, ?_⟩
      intro e he a ha
      obtain ⟨e', he', rfl⟩ := he
      obtain ⟨_, ⟨c, hc, rfl⟩, rfl⟩ := hA₂AE ha
      have hcC : φ c ∈ C := hc
      have h1 : π e' ∈ E₀ := by rw [← hE'map]; exact ⟨e', he', rfl⟩
      have h2 : rhoL L (c : ↥N) (QuotientGroup.mk e') = QuotientGroup.mk e' :=
        hCfix (φ c) hcC _ h1
      have h3 := (rhoL_fix_iff L (c : ↥N) e').1 h2
      have h4 := O.inv_mem h3
      have h5 : ((e' : G)) * (((c : ↥N) : G)) * (e' : G)⁻¹ * (((c : ↥N) : G))⁻¹ =
          (((c : ↥N) : G) * (e' : G) * ((c : ↥N) : G)⁻¹ * (e' : G)⁻¹)⁻¹ := by group
      simpa [h5] using h4
  obtain ⟨A', hA'c, hA'le, ⟨e⟩⟩ := exists_centralizing_copy hq hq2 hp hp2 O A₂ EG hOpg
    (hA₂M.trans (hMN.trans hNO)) hELO hA₂el.isPGroup hEGel.isPGroup hA₂comm
  refine ⟨SG, EG, A', hSGL, hSGp, hSGmax, hEGS, hEGel, hEGcard, ?_, hA'c, ?_, ?_, S, hSp, hSidx, ?_⟩
  · exact hA'le.trans (sup_le hA₂M (hOL.trans hLM))
  · exact isElemAbelian_of_mulEquiv e hA₂el
  · rw [Nat.card_congr e.toEquiv, hA₂card]
  · have : SG.subgroupOf L = SL := Subgroup.comap_map_eq_self_of_injective L.subtype_injective SL
    rw [this]
    exact hSLmap

end CFSG.LocalAnalysis.UniquenessCase.UC6S846
