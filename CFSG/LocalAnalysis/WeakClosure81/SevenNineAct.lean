module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNineCompl
public import CFSG.LocalAnalysis.WeakClosure81.SevenCommI
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {V H E J : Subgroup G}

theorem mem_centralizer_of_conj_eq_conj_of_coprime {M : Subgroup G} {z j : G}
    (hj : j ∈ Subgroup.normalizer (M : Set G))
    (hzj : ∀ m ∈ M, z * m * z⁻¹ = j * m * j⁻¹) (hcop : Nat.Coprime (orderOf z) (orderOf j)) :
    z ∈ Subgroup.centralizer (M : Set G) := by
  have hpow : ∀ n : ℕ, ∀ m ∈ M, z ^ n * m * (z ^ n)⁻¹ = j ^ n * m * (j ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro m _; simp
    | succ n ih =>
      intro m hm
      have hjN : j ^ n ∈ Subgroup.normalizer (M : Set G) := pow_mem hj n
      have hm' : j ^ n * m * (j ^ n)⁻¹ ∈ M :=
        (Subgroup.mem_normalizer_iff.mp hjN m).mp hm
      calc z ^ (n + 1) * m * (z ^ (n + 1))⁻¹
          = z * (z ^ n * m * (z ^ n)⁻¹) * z⁻¹ := by group
        _ = z * (j ^ n * m * (j ^ n)⁻¹) * z⁻¹ := by rw [ih m hm]
        _ = j * (j ^ n * m * (j ^ n)⁻¹) * j⁻¹ := hzj _ hm'
        _ = j ^ (n + 1) * m * (j ^ (n + 1))⁻¹ := by group
  have hzpow : j ^ orderOf z ∈ Subgroup.centralizer (M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h := hpow (orderOf z) m hm
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h
    conv_lhs => rw [h]
    group
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (x := j) (n := orderOf z) hcop
  have hjC : j ∈ Subgroup.centralizer (M : Set G) := by
    rw [← hk]
    exact pow_mem hzpow k
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  have h := hpow 1 m hm
  simp only [pow_one] at h
  have hjm : m * j = j * m := Subgroup.mem_centralizer_iff.mp hjC m hm
  have hzm : z * m * z⁻¹ = m := by
    rw [h, show j * m = m * j from hjm.symm]
    group
  conv_lhs => rw [← hzm]
  group

theorem SevenNineCompl.exists_conj (h : Hyp73 V H E J) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ) {L : Subgroup X} {p : ℕ}
    {Yb Zb : Subgroup X} (hc : SevenNineConfig L (barSub (kSub V H E) φ V) p Yb Zb) {v : G}
    (hvV : v ∈ V) (hvJ : v ∉ J) {P : Subgroup G} (hP : SevenNineCompl (kSub V H E) J φ Yb v P)
    {B : Subgroup G} (hB : B ≤ P) (hBcard : Nat.card B * p = Nat.card P) :
    ∃ g ∈ Subgroup.normalizer (iSub V H E : Set G), g ∈ Subgroup.normalizer (P : Set G) ∧
      conjSubgroup B g ≠ P ⊓ Subgroup.centralizer ({v} : Set G) ∧
      ¬ ⁅P, Subgroup.zpowers v⁆ ≤ conjSubgroup B g := by
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hJH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hHJ : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJH h.jnormal
  have hIH : iSub V H E ≤ H := h.iSub_le.trans hJH
  have hHI : H ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIH (iSub_subgroupOf_normal h.le h.normal)
  have hBb_le : barSub (kSub V H E) φ B ≤ Yb := by
    rw [← SevenNineCompl.barSub_eq hφ hP]
    exact Subgroup.map_mono (Subgroup.comap_mono hB)
  have hPcard : Nat.card P = Nat.card Yb := by
    rw [← SevenNineCompl.barSub_eq hφ hP]
    exact (SevenNineCompl.card_barSub_of_le hφ hP le_rfl).symm
  have hBbcard : Nat.card (barSub (kSub V H E) φ B) * p = Nat.card Yb := by
    rw [SevenNineCompl.card_barSub_of_le hφ hP hB, hBcard, hPcard]
  obtain ⟨hb, _hhbL, hhbN, hhb_ne, hhb_notle⟩ :=
    hc.exists_conj (barSub (kSub V H E) φ B) hBb_le hBbcard
  obtain ⟨h₀, hh₀⟩ := hφ.surjective hb
  have hY : (h₀ : G) ∈ Subgroup.normalizer (barPre (kSub V H E) φ Yb : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨hgK, hgYb⟩ := mem_barPre.mp hg
      have hmem : (h₀ : G) * g * (h₀ : G)⁻¹ ∈ kSub V H E :=
        (kSub V H E).mul_mem ((kSub V H E).mul_mem h₀.2 hgK) ((kSub V H E).inv_mem h₀.2)
      refine mem_barPre.mpr ⟨hmem, ?_⟩
      have hphi : φ (⟨(h₀ : G) * g * (h₀ : G)⁻¹, hmem⟩ : ↥(kSub V H E)) =
          hb * φ ⟨g, hgK⟩ * hb⁻¹ := by
        rw [show (⟨(h₀ : G) * g * (h₀ : G)⁻¹, hmem⟩ : ↥(kSub V H E)) =
            h₀ * ⟨g, hgK⟩ * h₀⁻¹ from Subtype.ext rfl, map_mul, map_mul, map_inv, hh₀]
      rw [hphi]
      exact (Subgroup.mem_normalizer_iff.mp hhbN (φ ⟨g, hgK⟩)).mp hgYb
    · intro hg
      obtain ⟨hgK, hgYb⟩ := mem_barPre.mp hg
      have hgK' : g ∈ kSub V H E := by
        have hmem : (h₀ : G)⁻¹ * ((h₀ : G) * g * (h₀ : G)⁻¹) * (h₀ : G) ∈ kSub V H E :=
          (kSub V H E).mul_mem
            ((kSub V H E).mul_mem ((kSub V H E).inv_mem h₀.2) hgK) h₀.2
        convert hmem using 1
        group
      refine mem_barPre.mpr ⟨hgK', ?_⟩
      have hphi : φ (⟨g, hgK'⟩ : ↥(kSub V H E)) =
          hb⁻¹ * φ ⟨(h₀ : G) * g * (h₀ : G)⁻¹, hgK⟩ * hb := by
        have heq : (⟨g, hgK'⟩ : ↥(kSub V H E)) =
            h₀⁻¹ * ⟨(h₀ : G) * g * (h₀ : G)⁻¹, hgK⟩ * h₀ :=
          Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
        rw [heq]
        simp only [map_mul, map_inv, hh₀]
      rw [hphi]
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhbN)
        (φ ⟨(h₀ : G) * g * (h₀ : G)⁻¹, hgK⟩)).mp hgYb
  have hJ : (h₀ : G) ∈ Subgroup.normalizer (J : Set G) := hHJ (hKH h₀.2)
  have hC : (h₀ : G) ∈
      Subgroup.normalizer ((barPre (kSub V H E) φ Yb ⊓ J : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hxY, hxJ⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hY x).mp hxY,
        (Subgroup.mem_normalizer_iff.mp hJ x).mp hxJ⟩
    · intro hx
      obtain ⟨hxY, hxJ⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hY x).mpr hxY,
        (Subgroup.mem_normalizer_iff.mp hJ x).mpr hxJ⟩
  have hconjY : (barPre (kSub V H E) φ Yb).map (MulAut.conj (h₀ : G)⁻¹).toMonoidHom =
      barPre (kSub V H E) φ Yb := conjSubgroup_eq_iff_mem_normalizer.mpr hY
  have hconjC : (barPre (kSub V H E) φ Yb ⊓ J).map (MulAut.conj (h₀ : G)⁻¹).toMonoidHom =
      barPre (kSub V H E) φ Yb ⊓ J := conjSubgroup_eq_iff_mem_normalizer.mpr hC
  have hP₂_le : conjSubgroup P (h₀ : G) ≤ barPre (kSub V H E) φ Yb :=
    calc conjSubgroup P (h₀ : G) ≤ conjSubgroup (barPre (kSub V H E) φ Yb) (h₀ : G) :=
          Subgroup.map_mono hP.le
      _ = barPre (kSub V H E) φ Yb := hconjY
  have hYnormC : barPre (kSub V H E) φ Yb ≤
      Subgroup.normalizer ((barPre (kSub V H E) φ Yb ⊓ J : Subgroup G) : Set G) := by
    intro y hy
    have hyH : y ∈ H := hKH (barPre_le (kSub V H E) φ Yb hy)
    have hyN : y ∈ Subgroup.normalizer (J : Set G) := hHJ hyH
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hxY, hxJ⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr
        ⟨(barPre (kSub V H E) φ Yb).mul_mem
            ((barPre (kSub V H E) φ Yb).mul_mem hy hxY)
            ((barPre (kSub V H E) φ Yb).inv_mem hy),
          (Subgroup.mem_normalizer_iff.mp hyN x).mp hxJ⟩
    · intro hx
      obtain ⟨hxY, hxJ⟩ := Subgroup.mem_inf.mp hx
      have hyiN : y⁻¹ ∈ Subgroup.normalizer (J : Set G) :=
        (Subgroup.normalizer (J : Set G)).inv_mem hyN
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [show x = y⁻¹ * (y * x * y⁻¹) * y by group]
        exact (barPre (kSub V H E) φ Yb).mul_mem
          ((barPre (kSub V H E) φ Yb).mul_mem
            ((barPre (kSub V H E) φ Yb).inv_mem hy) hxY) hy
      · have hxJ' : y⁻¹ * (y * x * y⁻¹) * y ∈ J := by
          simpa using (Subgroup.mem_normalizer_iff.mp hyiN (y * x * y⁻¹)).mp hxJ
        rwa [show y⁻¹ * (y * x * y⁻¹) * y = x by group] at hxJ'
  have hP₂_inf : (barPre (kSub V H E) φ Yb ⊓ J) ⊓ conjSubgroup P (h₀ : G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxC, hxP₂⟩ := Subgroup.mem_inf.mp hx
    have hxP : (h₀ : G) * x * (h₀ : G)⁻¹ ∈ P := mem_conjSubgroup_iff.mp hxP₂
    have hxC' : (h₀ : G) * x * (h₀ : G)⁻¹ ∈ barPre (kSub V H E) φ Yb ⊓ J :=
      (Subgroup.mem_normalizer_iff.mp hC x).mp hxC
    have h1 : (h₀ : G) * x * (h₀ : G)⁻¹ = 1 := by
      have hmem : (h₀ : G) * x * (h₀ : G)⁻¹ ∈ P ⊓ (barPre (kSub V H E) φ Yb ⊓ J) :=
        Subgroup.mem_inf.mpr ⟨hxP, hxC'⟩
      rwa [hP.inf_eq, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    calc x = (h₀ : G)⁻¹ * ((h₀ : G) * x * (h₀ : G)⁻¹) * (h₀ : G) := by group
      _ = 1 := by rw [h1]; group
  have hP₂_sup : (barPre (kSub V H E) φ Yb ⊓ J) ⊔ conjSubgroup P (h₀ : G) =
      barPre (kSub V H E) φ Yb := by
    apply le_antisymm
    · exact sup_le inf_le_left hP₂_le
    · calc barPre (kSub V H E) φ Yb
          = (barPre (kSub V H E) φ Yb).map (MulAut.conj (h₀ : G)⁻¹).toMonoidHom :=
            hconjY.symm
        _ = (P ⊔ (barPre (kSub V H E) φ Yb ⊓ J)).map
              (MulAut.conj (h₀ : G)⁻¹).toMonoidHom := by rw [hP.sup_eq]
        _ = P.map (MulAut.conj (h₀ : G)⁻¹).toMonoidHom ⊔
              (barPre (kSub V H E) φ Yb ⊓ J).map (MulAut.conj (h₀ : G)⁻¹).toMonoidHom :=
            Subgroup.map_sup _ _ _
        _ = conjSubgroup P (h₀ : G) ⊔ (barPre (kSub V H E) φ Yb ⊓ J) := by
            rw [hconjC]; rfl
        _ ≤ (barPre (kSub V H E) φ Yb ⊓ J) ⊔ conjSubgroup P (h₀ : G) :=
            le_of_eq (sup_comm _ _).symm
  haveI : Fact p.Prime := Fact.mk hc.prime
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  have hJ2 : IsPGroup 2 J := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le h.pcore_le
  have hYb_pgroup : IsPGroup p Yb := fun y => ⟨1, by
    have hy : (y : X) ^ p = 1 := hc.elemAbelian.2 y y.2
    rw [pow_one]
    exact Subtype.ext (by simpa using hy)⟩
  have hφ' : IsBarMap (kSub V H E) (kSub V H E ⊓ J) φ :=
    ⟨hφ.surjective, fun k => (hφ.ker_iff k).trans ⟨fun hk => ⟨k.2, hk⟩, fun hk => hk.2⟩⟩
  have hrelC : (barPre (kSub V H E) φ Yb ⊓ J).relIndex (barPre (kSub V H E) φ Yb) =
      Nat.card Yb := by
    have h₁ : (barPre (kSub V H E) φ Yb ⊓ J).relIndex (barPre (kSub V H E) φ Yb) =
        J.relIndex (barPre (kSub V H E) φ Yb) := inf_relIndex_left _ _
    have h₂ : J.relIndex (barPre (kSub V H E) φ Yb) =
        (kSub V H E ⊓ J).relIndex (barPre (kSub V H E) φ Yb) := by
      rw [← inf_relIndex_left (H := barPre (kSub V H E) φ Yb) (K := J),
        ← inf_relIndex_left (H := barPre (kSub V H E) φ Yb) (K := kSub V H E ⊓ J)]
      rw [show barPre (kSub V H E) φ Yb ⊓ (kSub V H E ⊓ J) =
          barPre (kSub V H E) φ Yb ⊓ J by
        rw [← inf_assoc, inf_eq_left.mpr (barPre_le (kSub V H E) φ Yb)]]
    rw [h₁, h₂]
    exact relIndex_barPre inf_le_left hφ' Yb
  have hcop : Nat.Coprime (Nat.card ↥(barPre (kSub V H E) φ Yb ⊓ J))
      ((barPre (kSub V H E) φ Yb ⊓ J).relIndex (barPre (kSub V H E) φ Yb)) := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp (hJ2.to_le inf_le_right)
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := p)).mp hYb_pgroup
    rw [ha, hrelC, hb]
    exact Nat.coprime_pow_primes a b Nat.prime_two hc.prime hc.ne_two.symm
  obtain ⟨c, hcC, hcP⟩ := CFSG.Walter.W67.Sec6.exists_conj_complement_in
    (C := barPre (kSub V H E) φ Yb ⊓ J) (N := barPre (kSub V H E) φ Yb)
    (W₁ := P) (W₂ := conjSubgroup P (h₀ : G))
    inf_le_left hYnormC hcop hP.le hP₂_le
    (by rw [inf_comm]; exact hP.inf_eq) (by rw [sup_comm]; exact hP.sup_eq) hP₂_inf hP₂_sup
  have hcK : c ∈ kSub V H E := barPre_le (kSub V H E) φ Yb hcC.1
  have hgH : (h₀ : G) * c ∈ H := H.mul_mem (hKH h₀.2) (hKH hcK)
  have hgN_I : (h₀ : G) * c ∈ Subgroup.normalizer (iSub V H E : Set G) := hHI hgH
  have hgN_P : (h₀ : G) * c ∈ Subgroup.normalizer (P : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp (by
      rw [← conjSubgroup_conjSubgroup P (h₀ : G) c, hcP]
      ext x
      rw [mem_conjSubgroup_iff, CFSG.Walter.W67.Sec6.mem_cj]
      simp only [show c⁻¹ * (c * x * c⁻¹) * c = x by group])
  let g' : ↥(kSub V H E) := h₀ * ⟨c, hcK⟩
  have hg'φ : φ g' = hb := by
    have hcφ : φ (⟨c, hcK⟩ : ↥(kSub V H E)) = 1 := (hφ.ker_iff _).mpr hcC.2
    rw [show g' = h₀ * ⟨c, hcK⟩ from rfl, map_mul, hcφ, mul_one, hh₀]
  have hbar : barSub (kSub V H E) φ (conjSubgroup B ((h₀ : G) * c)) =
      conjSubgroup (barSub (kSub V H E) φ B) hb := by
    rw [show (h₀ : G) * c = (g' : G) from rfl, barSub_conjSubgroup, hg'φ]
  refine ⟨(h₀ : G) * c, hgN_I, hgN_P, ?_, ?_⟩
  · intro heq
    exact hhb_ne (by
      rw [← hbar, heq, SevenNineCompl.barSub_inf_centralizer h hφ hc hvV hvJ hP])
  · intro hle
    exact hhb_notle (by
      rw [← SevenNineCompl.barSub_commutator h hφ hc hvV hvJ hP, ← hbar]
      exact Subgroup.map_mono (Subgroup.comap_mono hle))


theorem SevenNineCompl.commutator_iSub_le_centralizer (h : Hyp73 V H E J) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ) {L : Subgroup X} {p : ℕ}
    {Yb Zb : Subgroup X} (hc : SevenNineConfig L (barSub (kSub V H E) φ V) p Yb Zb) {v : G}
    (hvV : v ∈ V) (hvJ : v ∉ J) {P : Subgroup G} (hP : SevenNineCompl (kSub V H E) J φ Yb v P) :
    ⁅iSub V H E, Subgroup.zpowers v⁆ ≤
      Subgroup.centralizer ((P ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) := by
  have hJH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hIH : iSub V H E ≤ H := h.iSub_le.trans hJH
  have hHI : H ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIH (iSub_subgroupOf_normal h.le h.normal)
  have hJ2 : IsPGroup 2 J := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le h.pcore_le
  rw [Subgroup.le_centralizer_iff]
  intro z hz
  obtain ⟨hzP, hzC⟩ := Subgroup.mem_inf.mp hz
  have hzY : z ∈ barPre (kSub V H E) φ Yb := hP.le hzP
  have hzK : z ∈ kSub V H E := barPre_le (kSub V H E) φ Yb hzY
  have hzH : z ∈ H := hKH hzK
  have hzNI : z ∈ Subgroup.normalizer (iSub V H E : Set G) := hHI hzH
  have hzv : z * v * z⁻¹ = v := by
    have hcomm : z * v = v * z := Subgroup.mem_centralizer_singleton_iff.mp hzC
    rw [hcomm]; group
  have hMleV : ⁅iSub V H E, Subgroup.zpowers v⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (commutator_mem_inf_iSub h.elemAbelian h.ti h.abelian h.le h.normal h.omega_le
      h.mem ha (Subgroup.zpowers_le.mpr hvV hb)).1
  have hzbarZb : φ ⟨z, hzK⟩ ∈ Zb := by
    rw [← SevenNineCompl.barSub_inf_centralizer h hφ hc hvV hvJ hP]
    exact mem_barSub.mpr ⟨⟨z, hzK⟩, hz, rfl⟩
  have hzbarCC : φ ⟨z, hzK⟩ ∈ barSub (kSub V H E) φ (commConjSup V H E) :=
    le_barSub_commConjSup h hφ hc hzbarZb
  obtain ⟨r, hrCC, hrφ⟩ := mem_barSub.mp hzbarCC
  have hrCentV : (r : G) ∈ Subgroup.centralizer (V : Set G) :=
    commConjSup_le_centralizer V H E hrCC
  have hjJ : (r : G)⁻¹ * z ∈ J := by
    have h1 : φ (r⁻¹ * ⟨z, hzK⟩) = 1 := by
      rw [map_mul, map_inv, hrφ]
      group
    exact (hφ.ker_iff (r⁻¹ * ⟨z, hzK⟩)).mp h1
  have hzNzv : z ∈ Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact (MonoidHom.map_zpowers (MulAut.conj z) v).trans
      (congrArg (fun w : G => Subgroup.zpowers w) hzv)
  have hzNM : z ∈
      Subgroup.normalizer ((⁅iSub V H E, Subgroup.zpowers v⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hzNI,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hzNzv]
  have hzj : ∀ m ∈ ⁅iSub V H E, Subgroup.zpowers v⁆,
      z * m * z⁻¹ = ((r : G)⁻¹ * z) * m * ((r : G)⁻¹ * z)⁻¹ := by
    intro m hm
    have hzmM : z * m * z⁻¹ ∈ ⁅iSub V H E, Subgroup.zpowers v⁆ :=
      (Subgroup.mem_normalizer_iff.mp hzNM m).mp hm
    have hzmV : z * m * z⁻¹ ∈ V := hMleV hzmM
    have hcomm : (z * m * z⁻¹) * (r : G) = (r : G) * (z * m * z⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hrCentV _ hzmV
    calc z * m * z⁻¹ = (r : G)⁻¹ * ((r : G) * (z * m * z⁻¹)) := by group
      _ = (r : G)⁻¹ * ((z * m * z⁻¹) * (r : G)) := by rw [hcomm]
      _ = ((r : G)⁻¹ * z) * m * ((r : G)⁻¹ * z)⁻¹ := by group
  have hjNM : (r : G)⁻¹ * z ∈
      Subgroup.normalizer ((⁅iSub V H E, Subgroup.zpowers v⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · intro hm
      rw [← hzj m hm]
      exact (Subgroup.mem_normalizer_iff.mp hzNM m).mp hm
    · intro hm
      have h1 : (r : G)⁻¹ * (z * m * z⁻¹) * (r : G) ∈
          ⁅iSub V H E, Subgroup.zpowers v⁆ := by
        rwa [show ((r : G)⁻¹ * z) * m * ((r : G)⁻¹ * z)⁻¹ =
            (r : G)⁻¹ * (z * m * z⁻¹) * (r : G) by group] at hm
      have h1V : (r : G)⁻¹ * (z * m * z⁻¹) * (r : G) ∈ V := hMleV h1
      have hcomm1 : ((r : G)⁻¹ * (z * m * z⁻¹) * (r : G)) * (r : G) =
          (r : G) * ((r : G)⁻¹ * (z * m * z⁻¹) * (r : G)) :=
        Subgroup.mem_centralizer_iff.mp hrCentV _ h1V
      have h2 : z * m * z⁻¹ ∈ ⁅iSub V H E, Subgroup.zpowers v⁆ := by
        have heq : (r : G)⁻¹ * (z * m * z⁻¹) * (r : G) =
            (r : G) * ((r : G)⁻¹ * (z * m * z⁻¹) * (r : G)) * (r : G)⁻¹ := by
          rw [← hcomm1]; group
        rw [show z * m * z⁻¹ =
            (r : G) * ((r : G)⁻¹ * (z * m * z⁻¹) * (r : G)) * (r : G)⁻¹ by group,
          ← heq]
        exact h1
      have h3 : z⁻¹ * (z * m * z⁻¹) * z ∈ ⁅iSub V H E, Subgroup.zpowers v⁆ := by
        simpa using
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hzNM) (z * m * z⁻¹)).mp h2
      rwa [show z⁻¹ * (z * m * z⁻¹) * z = m by group] at h3
  have hz_pow : z ^ p = 1 := (SevenNineCompl.isElemAbelian hφ hc hP).2 z hzP
  have hzorder : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hz_pow
  obtain ⟨k, hk⟩ := hJ2 ⟨(r : G)⁻¹ * z, hjJ⟩
  have hj_pow : ((r : G)⁻¹ * z) ^ (2 ^ k) = 1 := by
    have h := congrArg (Subtype.val) hk
    simpa using h
  have hjorder : orderOf ((r : G)⁻¹ * z) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hj_pow
  have hcop : Nat.Coprime (orderOf z) (orderOf ((r : G)⁻¹ * z)) :=
    (((Nat.coprime_primes hc.prime Nat.prime_two).mpr hc.ne_two).pow_right k).coprime_dvd_left
      hzorder |>.coprime_dvd_right hjorder
  exact mem_centralizer_of_conj_eq_conj_of_coprime hjNM hzj hcop

theorem SevenNineCompl.commutator_iSub_ne_bot (h : Hyp73 V H E J) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ) {L : Subgroup X} {p : ℕ}
    {Yb Zb : Subgroup X} (hc : SevenNineConfig L (barSub (kSub V H E) φ V) p Yb Zb) {v : G}
    (hvV : v ∈ V) (hvJ : v ∉ J) {P : Subgroup G} (hP : SevenNineCompl (kSub V H E) J φ Yb v P) :
    ⁅iSub V H E, P⁆ ≠ ⊥ := by
  intro hbot
  have hJH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hPcent : P ≤ Subgroup.centralizer (iSub V H E : Set G) :=
    (Subgroup.le_centralizer_iff (H := P) (K := iSub V H E)).mpr
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
  have hPK : P ≤ kSub V H E := hP.le.trans (barPre_le (kSub V H E) φ Yb)
  have hvK : v ∈ kSub V H E := le_kSub h.mem hvV
  have hP_le_Cv : P ≤ Subgroup.centralizer ({v} : Set G) := by
    intro x hxP
    have hxK : x ∈ kSub V H E := hPK hxP
    have hcomm : ⁅x, v⁆ ∈ iSub V H E :=
      commutator_centralizer_iSub_kSub_le h.elemAbelian h.ti h.abelian h.le h.normal h.omega_le
        (Subgroup.commutator_mem_commutator
          (Subgroup.mem_inf.mpr ⟨hxK, hPcent hxP⟩) hvK)
    have hx'v' : φ (⁅(⟨x, hxK⟩ : ↥(kSub V H E)), (⟨v, hvK⟩ : ↥(kSub V H E))⁆) = 1 :=
      (hφ.ker_iff _).mpr (by
        have hcoe : ((⁅(⟨x, hxK⟩ : ↥(kSub V H E)), (⟨v, hvK⟩ : ↥(kSub V H E))⁆ :
            ↥(kSub V H E)) : G) = ⁅x, v⁆ := rfl
        rw [hcoe]
        exact h.iSub_le hcomm)
    have hvxv : φ ((⟨v, hvK⟩ : ↥(kSub V H E)) * (⟨x, hxK⟩ : ↥(kSub V H E)) *
        (⟨v, hvK⟩ : ↥(kSub V H E))⁻¹) = φ (⟨x, hxK⟩ : ↥(kSub V H E)) := by
      have hcomm' : φ (⟨v, hvK⟩ : ↥(kSub V H E)) * φ (⟨x, hxK⟩ : ↥(kSub V H E)) =
          φ (⟨x, hxK⟩ : ↥(kSub V H E)) * φ (⟨v, hvK⟩ : ↥(kSub V H E)) := by
        have h1 : ⁅φ (⟨x, hxK⟩ : ↥(kSub V H E)), φ (⟨v, hvK⟩ : ↥(kSub V H E))⁆ = 1 := by
          rw [← map_commutatorElement, hx'v']
        exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
      rw [map_mul, map_mul, map_inv, hcomm']
      group
    have hvxP : v * x * v⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hP.mem_normalizer x).mp hxP
    have hphi : φ (⟨v * x * v⁻¹, (kSub V H E).mul_mem ((kSub V H E).mul_mem hvK hxK)
        ((kSub V H E).inv_mem hvK)⟩ : ↥(kSub V H E)) = φ (⟨x, hxK⟩ : ↥(kSub V H E)) := by
      have heq : (⟨v * x * v⁻¹, (kSub V H E).mul_mem ((kSub V H E).mul_mem hvK hxK)
            ((kSub V H E).inv_mem hvK)⟩ : ↥(kSub V H E)) =
          (⟨v, hvK⟩ : ↥(kSub V H E)) * (⟨x, hxK⟩ : ↥(kSub V H E)) *
            (⟨v, hvK⟩ : ↥(kSub V H E))⁻¹ := Subtype.ext rfl
      rw [heq, hvxv]
    have hveq : v * x * v⁻¹ = x :=
      congrArg Subtype.val (SevenNineCompl.injective hφ hP hvxP hxP hphi)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * v = (v * x * v⁻¹) * v := by rw [hveq]
      _ = v * x := by group
  have hinf : P ⊓ Subgroup.centralizer ({v} : Set G) = P := inf_eq_left.mpr hP_le_Cv
  have hcard := SevenNineCompl.card_inf_centralizer h hφ hc hvV hvJ hP
  rw [hinf] at hcard
  exact hc.prime.ne_one (Nat.mul_left_cancel (Nat.card_pos (α := ↥P)) (by simpa using hcard))

end CFSG.LocalAnalysis.WeakClosure81
