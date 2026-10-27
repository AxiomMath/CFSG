module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

@[expose] def S1614Hyp2iii (D : FFModel) : Prop :=
  ∀ H : Subgroup D.Amb, D.ker ≤ H → H ≤ D.sec → 2 * Nat.card ↥H = Nat.card ↥D.sec →
    ∃ X : Subgroup D.Amb, D.ker ≤ X ∧ X ≤ H ∧ Nat.card ↥X = 4 * Nat.card ↥D.ker ∧
      ∃ E : Subgroup D.Gam, IsElemAbelian 3 E ∧ 9 ≤ Nat.card ↥E ∧
        (∀ e ∈ E, ∀ x ∈ X, D.act e x ∈ X) ∧
        ∀ e ∈ E, (∀ m ∈ D.sec, D.act e m * m⁻¹ ∈ D.ker) → e = 1

@[expose] def S1614Hyp2iiiMod {W : Type} [CommGroup W] (H : Subgroup (MulAut W))
    (J : Subgroup W) : Prop :=
  ∀ J₀ : Subgroup W, J₀ ≤ J → 2 * Nat.card ↥J₀ = Nat.card ↥J →
    ∃ X : Subgroup W, X ≤ J₀ ∧ Nat.card ↥X = 4 ∧ ∃ E : Subgroup (MulAut W), E ≤ H ∧
      IsElemAbelian 3 E ∧ 9 ≤ Nat.card ↥E ∧ ∀ e ∈ E, X.map e.toMonoidHom = X

theorem s1614_transport {W : Type} [CommGroup W] [Finite W] {D : FFModel} [Finite D.Amb]
    (hD : S1614Hyp2iii D) {H : Subgroup (MulAut W)} {J : Subgroup W}
    (hR : D.Realizes H J ⊥) : S1614Hyp2iiiMod H J := by
  classical
  unfold S1614Hyp2iiiMod
  intro J₀ hJ₀ hcard
  rcases hR with ⟨π, hπs, -, hkerle, hJinv, -, hsec, hkerI, β, hβs, hβk, hβe⟩
  haveI : Nonempty ↥J₀ := ⟨1⟩
  haveI : Nonempty ↥D.ker := ⟨1⟩
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one β]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  let S : Subgroup ↥J := J₀.subgroupOf J
  have hcardS : Nat.card ↥S = Nat.card ↥J₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ₀).toEquiv
  have hSindex : S.index = 2 := by
    have h := Subgroup.card_mul_index S
    rw [hcardS, ← hcard] at h
    have h2 : Nat.card ↥J₀ * S.index = Nat.card ↥J₀ * 2 := by
      rw [h, mul_comm 2]
    exact Nat.mul_left_cancel (Nat.card_pos (α := ↥J₀)) h2
  let S' : Subgroup (↥D.sec ⧸ D.ker.subgroupOf D.sec) := S.map β
  let q : ↥D.sec →* (↥D.sec ⧸ D.ker.subgroupOf D.sec) :=
    QuotientGroup.mk' (D.ker.subgroupOf D.sec)
  let K : Subgroup ↥D.sec := S'.comap q
  let H' : Subgroup D.Amb := K.map D.sec.subtype
  have hS'index : S'.index = 2 := by
    change (S.map β).index = 2
    rw [Subgroup.index_map_of_bijective ⟨hβinj, hβs⟩ S, hSindex]
  have hKindex : K.index = 2 := by
    change (S'.comap q).index = 2
    rw [Subgroup.index_comap_of_surjective S' (QuotientGroup.mk'_surjective _), hS'index]
  have hKcard : 2 * Nat.card ↥K = Nat.card ↥D.sec := by
    have h := Subgroup.card_mul_index K
    rw [hKindex] at h
    rw [mul_comm]
    exact h
  have hH'card : Nat.card ↥H' = Nat.card ↥K :=
    Subgroup.card_map_of_injective (K := K) (f := D.sec.subtype) D.sec.subtype_injective
  have h2 : 2 * Nat.card ↥H' = Nat.card ↥D.sec := by
    rw [hH'card]
    exact hKcard
  have hkerH' : D.ker ≤ H' := by
    intro m hm
    change m ∈ K.map D.sec.subtype
    have hmk' : (⟨m, hkerle hm⟩ : ↥D.sec) ∈ K := by
      change (⟨m, hkerle hm⟩ : ↥D.sec) ∈ S'.comap q
      rw [Subgroup.mem_comap]
      have hmk : (⟨m, hkerle hm⟩ : ↥D.sec) ∈ q.ker := by
        rw [show q.ker = D.ker.subgroupOf D.sec from QuotientGroup.ker_mk' _]
        exact hm
      rw [MonoidHom.mem_ker.1 hmk]
      exact S'.one_mem
    exact Subgroup.mem_map_of_mem D.sec.subtype hmk'
  have hH'le : H' ≤ D.sec := by
    intro x hx
    change x ∈ K.map D.sec.subtype at hx
    rcases Subgroup.mem_map.1 hx with ⟨y, -, rfl⟩
    exact y.2
  obtain ⟨X, hkerX, hXH', hXcard, E, hEab, hE9, hEstab, hEfaith⟩ :=
    hD H' hkerH' hH'le h2
  have hXsec : X ≤ D.sec := le_trans hXH' hH'le
  let X' : Subgroup ↥D.sec := X.subgroupOf D.sec
  have hX'card : Nat.card ↥X' = 4 * Nat.card ↥D.ker := by
    have h : Nat.card ↥X' = Nat.card ↥X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXsec).toEquiv
    rw [h, hXcard]
  have hkerX' : D.ker.subgroupOf D.sec ≤ X' := by
    intro y hy
    exact hkerX (Subgroup.mem_subgroupOf.1 hy)
  have hX'qcard : Nat.card (X'.map q) = 4 := by
    have h1 := Subgroup.relIndex_mul_card q.ker X'
    rw [Subgroup.relIndex_ker X' q] at h1
    have hkerq : q.ker = D.ker.subgroupOf D.sec := QuotientGroup.ker_mk' _
    have hinf : q.ker ⊓ X' = q.ker := by
      rw [hkerq]
      exact inf_eq_left.mpr hkerX'
    rw [hinf, hkerq] at h1
    have hqcard : Nat.card ↥(D.ker.subgroupOf D.sec) = Nat.card ↥D.ker :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv
    rw [hqcard, hX'card] at h1
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥D.ker)) h1
  let X₀ : Subgroup W := ((X'.map q).comap β).map J.subtype
  have hmemX₀ : ∀ u : W, u ∈ X₀ ↔ ∃ (hu : u ∈ J), β ⟨u, hu⟩ ∈ X'.map q := by
    intro u
    change u ∈ ((X'.map q).comap β).map J.subtype ↔
      ∃ (hu : u ∈ J), β ⟨u, hu⟩ ∈ X'.map q
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨v, hv, hvu⟩
      rw [Subgroup.mem_comap] at hv
      have hu : u ∈ J := by
        rw [← hvu]
        exact v.2
      refine ⟨hu, ?_⟩
      have hthis : (⟨u, hu⟩ : ↥J) = v := Subtype.ext hvu.symm
      rwa [hthis]
    · rintro ⟨hu, hβu⟩
      exact ⟨⟨u, hu⟩, Subgroup.mem_comap.2 hβu, rfl⟩
  have hcomapβcard : Nat.card ↥((X'.map q).comap β) = 4 := by
    have hmap := Subgroup.map_comap_eq_self_of_surjective (f := β) hβs (X'.map q)
    have hcard := Subgroup.card_map_of_injective (K := (X'.map q).comap β) (f := β) hβinj
    rw [hmap, hX'qcard] at hcard
    exact hcard.symm
  have hX₀card : Nat.card ↥X₀ = 4 := by
    have h := Subgroup.card_map_of_injective (K := (X'.map q).comap β) (f := J.subtype)
      (Subgroup.subtype_injective J)
    rw [hcomapβcard] at h
    exact h
  have hX'q_le_S' : X'.map q ≤ S' := by
    intro y hy
    rcases Subgroup.mem_map.1 hy with ⟨x', hx', rfl⟩
    have hxX : (x' : D.Amb) ∈ X := hx'
    have hxH' : (x' : D.Amb) ∈ H' := hXH' hxX
    change (x' : D.Amb) ∈ K.map D.sec.subtype at hxH'
    rcases Subgroup.mem_map.1 hxH' with ⟨y', hy', hy'e⟩
    have hy'x' : y' = x' := Subtype.ext hy'e
    have hy'' : q y' ∈ S' := Subgroup.mem_comap.1 hy'
    rw [← hy'x']
    exact hy''
  have hX₀le : X₀ ≤ J₀ := by
    intro u hu
    obtain ⟨huJ, hβu⟩ := (hmemX₀ u).1 hu
    have hβuS' : β ⟨u, huJ⟩ ∈ S' := hX'q_le_S' hβu
    rcases Subgroup.mem_map.1 hβuS' with ⟨s, hs, hsv⟩
    have hsval : (s : W) ∈ J₀ := Subgroup.mem_subgroupOf.1 hs
    have hsu : (s : W) = u := congrArg Subtype.val (hβinj hsv)
    rw [hsu] at hsval
    exact hsval
  let ρ : D.Gam →* MulAut W := H.subtype.comp π
  have hρone : ∀ e ∈ E, ρ e = 1 → e = 1 := by
    intro e he hρe
    apply hEfaith e he
    intro m hm
    obtain ⟨u, hu⟩ := hβs (q ⟨m, hm⟩)
    have hu' : ((π e : ↥H) : MulAut W) (u : W) ∈ J := hJinv (π e) u u.2
    have hm' : D.act e (m : D.Amb) ∈ D.sec := hsec e m hm
    have hb := hβe e u ⟨m, hm⟩ hu' hm' hu
    have hπe : ((π e : ↥H) : MulAut W) = 1 := hρe
    have hL : β ⟨((π e : ↥H) : MulAut W) (u : W), hu'⟩ = β u := by
      have hxy : (⟨((π e : ↥H) : MulAut W) (u : W), hu'⟩ : ↥J) = u := by
        apply Subtype.ext
        show ((π e : ↥H) : MulAut W) (u : W) = (u : W)
        rw [hπe]
        exact MulAut.one_apply W (u : W)
      rw [hxy]
    rw [hL, hu] at hb
    have heq : QuotientGroup.mk (⟨m, hm⟩ : ↥D.sec) =
        QuotientGroup.mk (⟨D.act e (m : D.Amb), hm'⟩ : ↥D.sec) := hb
    have hmem : (⟨m, hm⟩ : ↥D.sec)⁻¹ * ⟨D.act e (m : D.Amb), hm'⟩ ∈
        D.ker.subgroupOf D.sec := (QuotientGroup.eq).1 heq
    have hmem' : m⁻¹ * D.act e (m : D.Amb) ∈ D.ker := by
      simpa using (Subgroup.mem_subgroupOf.1 hmem)
    rwa [mul_comm] at hmem'
  have hρinj : Function.Injective (ρ.comp E.subtype) := by
    rw [injective_iff_map_eq_one (ρ.comp E.subtype)]
    intro e he
    exact (Subgroup.subtype_injective E) (hρone (E.subtype e) e.2 he)
  have hmapE : (⊤ : Subgroup ↥E).map (ρ.comp E.subtype) = E.map ρ := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨E.subtype a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hEHcard : Nat.card ↥(E.map ρ) = Nat.card ↥E := by
    have h := Subgroup.card_map_of_injective (K := (⊤ : Subgroup ↥E))
      (f := ρ.comp E.subtype) hρinj
    rw [hmapE, Subgroup.card_top] at h
    exact h
  have hEH9 : 9 ≤ Nat.card ↥(E.map ρ) := by
    rw [hEHcard]
    exact hE9
  have hEHab : IsElemAbelian 3 (E.map ρ) := by
    refine ⟨?_, ?_⟩
    · haveI : IsMulCommutative ↥E := hEab.1
      infer_instance
    · intro x hx
      rcases Subgroup.mem_map.1 hx with ⟨e, he, rfl⟩
      show ρ e ^ 3 = 1
      rw [← map_pow, hEab.2 e he, map_one]
  have hEHle : E.map ρ ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.1 hx with ⟨e, -, rfl⟩
    exact (π e).2
  have hX₀stable : ∀ e ∈ E.map ρ, X₀.map e.toMonoidHom = X₀ := by
    intro eH heH
    rcases Subgroup.mem_map.1 heH with ⟨e, he, rfl⟩
    apply Subgroup.eq_of_le_of_card_ge
    · intro u hu
      rw [Subgroup.mem_map] at hu
      rcases hu with ⟨v, hv, rfl⟩
      change ρ e v ∈ X₀
      obtain ⟨hvJ, hβv⟩ := (hmemX₀ v).1 hv
      rw [hmemX₀ (ρ e v)]
      have hπvJ : ((π e : ↥H) : MulAut W) v ∈ J := hJinv (π e) v hvJ
      refine ⟨hπvJ, ?_⟩
      change β ⟨((π e : ↥H) : MulAut W) v, hπvJ⟩ ∈ X'.map q
      rw [Subgroup.mem_map] at hβv
      rcases hβv with ⟨x', hx', hx'e⟩
      have hactX : D.act e (x' : D.Amb) ∈ D.sec := hsec e x' x'.2
      have hactX' : (⟨D.act e (x' : D.Amb), hactX⟩ : ↥D.sec) ∈ X' :=
        hEstab e he (x' : D.Amb) hx'
      have hb := hβe e ⟨v, hvJ⟩ x' hπvJ hactX hx'e.symm
      rw [hb]
      exact Subgroup.mem_map_of_mem q hactX'
    · rw [Subgroup.card_map_of_injective (f := (ρ e).toMonoidHom) (ρ e).injective]
  exact ⟨X₀, hX₀le, hX₀card, E.map ρ, hEHle, hEHab, hEH9, hX₀stable⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
