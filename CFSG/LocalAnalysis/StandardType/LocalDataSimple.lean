module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MaxD2PermSound
public import CFSG.GroupActions.Iwasawa
public import CFSG.Open.Defs

public section

namespace CFSG.StandardType.LocalDataSimple

open CFSG.AGLEmbedding.MaxD2 (LocalData)
open scoped commutatorElement

variable {Q : Type*} [Group Q] [Finite Q]

theorem eq_bot_of_normal_le_normalizer {p m lam e : ℕ} (hp : p.Prime) (hm : 1 < m)
    {G R : Subgroup Q} (hloc : LocalData p m lam e G R)
    (hnn : ¬ G ≤ Subgroup.normalizer (R : Set Q))
    (hgen : G ≤ Subgroup.closure {x | ∃ g ∈ G, ∃ r ∈ R, x = g * r * g⁻¹})
    {K : Subgroup Q} (hKG : K ≤ G) (hKn : ∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hKB : K ≤ Subgroup.normalizer (R : Set Q)) : K = ⊥ := by
  obtain ⟨hRG, hRcard, -, hcent, -, t, htB, -, -, htor⟩ := hloc
  have htG : t ∈ G := htB.2
  have htnorm : t ∈ Subgroup.normalizer (R : Set Q) := htB.1
  have hDleK : K ⊓ R ≤ K := inf_le_left
  have hDleR : K ⊓ R ≤ R := inf_le_right
  have hDdvd : Nat.card (K ⊓ R : Subgroup Q) ∣ p ^ 2 := by
    rw [← hRcard]
    exact Subgroup.card_dvd_of_le hDleR
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).1 hDdvd
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk_cases with rfl | rfl | rfl
  ·
    have hDbot : K ⊓ R = ⊥ := Subgroup.eq_bot_of_card_eq (K ⊓ R) (by simpa using hk)
    rw [Subgroup.eq_bot_iff_forall]
    intro x hxK
    have hxG : x ∈ G := hKG hxK
    have hxR : x ∈ R := hcent x hxG (fun r hr => by
      apply commutatorElement_eq_one_iff_mul_comm.mp
      have hmemK : ⁅x, r⁆ ∈ K := by
        have h2 : r * x⁻¹ * r⁻¹ ∈ K := hKn r (hRG hr) x⁻¹ (inv_mem hxK)
        have h3 : x * (r * x⁻¹ * r⁻¹) ∈ K := mul_mem hxK h2
        simpa [commutatorElement_def, mul_assoc] using h3
      have hmemR : ⁅x, r⁆ ∈ R := by
        have h2 : x * r * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff (H := R)).mp (hKB hxK) r |>.mp hr
        have h3 : (x * r * x⁻¹) * r⁻¹ ∈ R := mul_mem h2 (inv_mem hr)
        simpa [commutatorElement_def, mul_assoc] using h3
      have hmem : ⁅x, r⁆ ∈ K ⊓ R := ⟨hmemK, hmemR⟩
      rw [hDbot] at hmem
      simpa using hmem)
    have hmem : x ∈ K ⊓ R := ⟨hxK, hxR⟩
    rw [hDbot] at hmem
    simpa using hmem
  ·
    have hDcard : Nat.card (K ⊓ R : Subgroup Q) = p := by simpa using hk
    have htmem : t ∈ Subgroup.normalizer ((K ⊓ R : Subgroup Q) : Set Q) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact ⟨hKn t htG x hx.1, (Subgroup.mem_normalizer_iff (H := R)).mp htnorm x |>.mp hx.2⟩
      · rintro ⟨hxK, hxR⟩
        refine ⟨?_, (Subgroup.mem_normalizer_iff (H := R)).mp htnorm x |>.mpr hxR⟩
        have h2 : t⁻¹ * (t * x * t⁻¹) * t ∈ K := by
          simpa using hKn t⁻¹ (inv_mem htG) (t * x * t⁻¹) hxK
        have heq : t⁻¹ * (t * x * t⁻¹) * t = x := by group
        rwa [heq] at h2
    exact absurd (by simpa using htmem) (htor 1 Nat.one_pos hm (K ⊓ R) hDleR hDcard)
  ·
    have hDcard : Nat.card (K ⊓ R : Subgroup Q) = p ^ 2 := by simpa using hk
    have hDR : K ⊓ R = R :=
      Subgroup.eq_of_le_of_card_ge hDleR (by rw [hDcard, hRcard])
    have hRK : R ≤ K := hDR ▸ inf_le_left
    apply absurd ?_ hnn
    refine hgen.trans ((Subgroup.closure_le (Subgroup.normalizer (R : Set Q))).mpr ?_)
    rintro x ⟨g, hg, r, hr, rfl⟩
    exact hKB (hKn g hg r (hRK hr))

theorem commutator_eq_top_of_localData {p m e : ℕ}
    {G R : Subgroup Q} (hloc : LocalData p m 2 e G R)
    (hgen : G ≤ Subgroup.closure {x | ∃ g ∈ G, ∃ r ∈ R, x = g * r * g⁻¹}) :
    commutator ↥G = ⊤ := by
  obtain ⟨hRG, -, -, -, -, t, htB, htact, -, -⟩ := hloc
  have htG : t ∈ G := htB.2
  set C : Subgroup Q := (commutator ↥G).map G.subtype with hC
  have hRsub : ∀ r ∈ R, r ∈ C := by
    intro r hr
    refine ⟨⁅(⟨t, htG⟩ : ↥G) ^ m, (⟨r, hRG hr⟩ : ↥G)⁆, ?_, ?_⟩
    · exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    · rw [map_commutatorElement]
      simp only [map_pow, Subgroup.subtype_apply, Subgroup.coe_mk]
      rw [commutatorElement_def, htact r hr]
      group
  have hRcomm : ∀ r (hr : r ∈ R), (⟨r, hRG hr⟩ : ↥G) ∈ commutator ↥G := by
    intro r hr
    obtain ⟨y, hy, hyeq⟩ := hRsub r hr
    have : y = (⟨r, hRG hr⟩ : ↥G) := Subtype.ext (by simpa using hyeq)
    rwa [this] at hy
  have hSC : {x | ∃ g ∈ G, ∃ r ∈ R, x = g * r * g⁻¹} ⊆ C := by
    rintro x ⟨g, hg, r, hr, rfl⟩
    refine ⟨(⟨g, hg⟩ : ↥G) * (⟨r, hRG hr⟩ : ↥G) * (⟨g, hg⟩ : ↥G)⁻¹, ?_, ?_⟩
    · exact (inferInstance : (commutator ↥G).Normal).conj_mem _ (hRcomm r hr) _
    · simp
  have hGleC : G ≤ C := hgen.trans ((Subgroup.closure_le C).mpr hSC)
  rw [eq_top_iff]
  intro g _
  have hg : (g : Q) ∈ C := hGleC g.2
  rw [hC] at hg
  obtain ⟨y, hy, hyeq⟩ := hg
  have : y = g := Subtype.ext hyeq
  rwa [this] at hy

theorem isSimpleGroup_of_localData {p m e : ℕ} (hp : p.Prime) (hm : 1 < m)
    {G R : Subgroup Q} (hloc : LocalData p m 2 e G R)
    (hnn : ¬ G ≤ Subgroup.normalizer (R : Set Q))
    (hgen : G ≤ Subgroup.closure {x | ∃ g ∈ G, ∃ r ∈ R, x = g * r * g⁻¹}) :
    IsSimpleGroup ↥G ∧ commutator ↥G = ⊤ := by
  have hloc' : LocalData p m 2 e G R := hloc
  obtain ⟨hRG, hRcard, hmax, -, -, t, htB, -, -, -⟩ := hloc
  let B : Subgroup Q := Subgroup.normalizer (R : Set Q) ⊓ G
  let B' : Subgroup ↥G := B.subgroupOf G
  have hBleG : B ≤ G := inf_le_right
  have hB'map : B'.map G.subtype = B := by
    change (B.subgroupOf G).map G.subtype = B
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBleG]
  have hB'ne : B' ≠ ⊤ := by
    intro h
    change B.subgroupOf G = ⊤ at h
    exact hnn ((Subgroup.subgroupOf_eq_top.mp h).trans inf_le_left)
  have hcoatom : IsCoatom B' := by
    refine ⟨hB'ne, ?_⟩
    intro Y hYlt
    have hBleYq : B ≤ Y.map G.subtype := by
      rw [← hB'map]
      exact Subgroup.map_mono hYlt.le
    have hYqle : Y.map G.subtype ≤ G := Subgroup.map_subtype_le Y
    have hstrict : B < Y.map G.subtype := by
      rw [← hB'map]
      exact (Subgroup.map_subtype_lt_map_subtype (G' := G)).mpr hYlt
    rcases hmax (Y.map G.subtype) hBleYq hYqle with hEq | hEq
    · exact absurd hEq.symm (ne_of_lt hstrict)
    · have hEqTop : Y.map G.subtype = (⊤ : Subgroup ↥G).map G.subtype := by
        rw [hEq, Subgroup.map_top G.subtype, Subgroup.range_subtype]
      exact (Subgroup.map_subtype_inj (H := G)).mp hEqTop
  haveI : Nontrivial ↥G := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    calc (1 : ℕ) < p ^ 2 := by nlinarith [hp.two_le]
      _ = Nat.card R := hRcard.symm
      _ ≤ Nat.card G := Subgroup.card_le_of_le hRG
  haveI : Nontrivial (↥G ⧸ B') := by
    rw [QuotientGroup.nontrivial_iff]
    exact hB'ne
  haveI : MulAction.IsPreprimitive ↥G (↥G ⧸ B') := by
    refine (MulAction.isCoatom_stabilizer_iff_preprimitive (G := ↥G) (X := ↥G ⧸ B')
      ((1 : ↥G) : ↥G ⧸ B')).mp ?_
    rw [MulAction.stabilizer_quotient B']
    exact hcoatom
  haveI : FaithfulSMul ↥G (↥G ⧸ B') := by
    have hKmem : ∀ k : ↥G, k ∈ (MulAction.toPermHom ↥G (↥G ⧸ B')).ker ↔
        ∀ x : ↥G ⧸ B', k • x = x := by
      intro k
      rw [MonoidHom.mem_ker, MulAction.toPermHom_apply]
      constructor
      · intro h x
        have hx := congrArg (fun e : Equiv.Perm (↥G ⧸ B') => e x) h
        simpa using hx
      · intro h
        ext x
        simpa using h x
    let Kq : Subgroup Q := (MulAction.toPermHom ↥G (↥G ⧸ B')).ker.map G.subtype
    have hKG : Kq ≤ G := Subgroup.map_subtype_le _
    have hKn : ∀ g ∈ G, ∀ k ∈ Kq, g * k * g⁻¹ ∈ Kq := by
      intro g hg k hk
      obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
      refine ⟨(⟨g, hg⟩ : ↥G) * k' * (⟨g, hg⟩ : ↥G)⁻¹, ?_, ?_⟩
      · exact (inferInstance : (MulAction.toPermHom ↥G (↥G ⧸ B')).ker.Normal).conj_mem k' hk' _
      · simp
    have hKB : Kq ≤ Subgroup.normalizer (R : Set Q) := by
      intro k hk
      obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
      have hstab : k' ∈ MulAction.stabilizer ↥G ((1 : ↥G) : ↥G ⧸ B') := by
        rw [MulAction.mem_stabilizer_iff]
        exact (hKmem k').mp hk' _
      have hB'mem : k' ∈ B' := by
        rw [← MulAction.stabilizer_quotient B']
        exact hstab
      have hkB : (G.subtype k') ∈ B := by
        rw [← hB'map]
        exact Subgroup.mem_map_of_mem G.subtype hB'mem
      change (G.subtype k') ∈ Subgroup.normalizer (R : Set Q) ⊓ G at hkB
      exact hkB.1
    have hKbot : Kq = ⊥ := eq_bot_of_normal_le_normalizer hp hm hloc' hnn hgen hKG hKn hKB
    refine ⟨fun {m₁ m₂} h => ?_⟩
    have hmem : m₂⁻¹ * m₁ ∈ (MulAction.toPermHom ↥G (↥G ⧸ B')).ker := by
      rw [hKmem]
      intro x
      rw [mul_smul, h x, inv_smul_smul]
    have hmap : G.subtype (m₂⁻¹ * m₁) ∈ Kq := Subgroup.mem_map_of_mem G.subtype hmem
    rw [hKbot] at hmap
    have h1 : G.subtype (m₂⁻¹ * m₁) = 1 := by simpa using hmap
    have h2 : m₂⁻¹ * m₁ = 1 := G.subtype_injective (by rw [h1, map_one])
    exact (inv_mul_eq_one.mp h2).symm
  let A : Subgroup ↥G := R.subgroupOf G
  have hAcard : Nat.card A = p ^ 2 := by
    change Nat.card (R.subgroupOf G) = p ^ 2
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRG).toEquiv, hRcard]
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative A :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := A) (p := p) hAcard
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hAn : ∀ h ∈ MulAction.stabilizer ↥G ((1 : ↥G) : ↥G ⧸ B'), ∀ a ∈ A,
      h * a * h⁻¹ ∈ A := by
    intro h hh a ha
    have hhB' : h ∈ B' := by
      rw [← MulAction.stabilizer_quotient B']
      exact hh
    have hhB : (h : Q) ∈ B := by
      rw [← hB'map]
      exact Subgroup.mem_map_of_mem G.subtype hhB'
    have haR : (a : Q) ∈ R := ha
    rw [Subgroup.mem_subgroupOf]
    have hnorm : (h : Q) ∈ Subgroup.normalizer (R : Set Q) := by
      change (h : Q) ∈ Subgroup.normalizer (R : Set Q) ⊓ G at hhB
      exact hhB.1
    simpa using (Subgroup.mem_normalizer_iff (H := R)).mp hnorm (a : Q) |>.mp haR
  have hgenN : Subgroup.normalClosure (A : Set ↥G) = ⊤ := by
    have hmap : (Subgroup.normalClosure (A : Set ↥G)).map G.subtype = G := by
      apply le_antisymm
      · exact Subgroup.map_subtype_le _
      · refine hgen.trans ((Subgroup.closure_le
          ((Subgroup.normalClosure (A : Set ↥G)).map G.subtype)).mpr ?_)
        rintro x ⟨g, hg, r, hr, rfl⟩
        refine ⟨(⟨g, hg⟩ : ↥G) * (⟨r, hRG hr⟩ : ↥G) * (⟨g, hg⟩ : ↥G)⁻¹, ?_, ?_⟩
        · exact (Subgroup.normalClosure_normal (s := (A : Set ↥G))).conj_mem _
            (Subgroup.subset_normalClosure (show (⟨r, hRG hr⟩ : ↥G) ∈ A from hr)) _
        · simp
    have htop : (⊤ : Subgroup ↥G).map G.subtype = G := by
      rw [Subgroup.map_top G.subtype, Subgroup.range_subtype]
    exact (Subgroup.map_subtype_inj (H := G)).mp (hmap.trans htop.symm)
  have hperf : commutator ↥G = ⊤ := commutator_eq_top_of_localData hloc' hgen
  exact ⟨CFSG.GroupActions.isSimpleGroup_of_iwasawa hperf ((1 : ↥G) : ↥G ⧸ B')
    hAn hAc hgenN, hperf⟩

end CFSG.StandardType.LocalDataSimple
