module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Residual

open CFSG.QuasithinUnique.Setup.X6

variable {X : Type} [Group X] [Finite X]

theorem dInf_eq_of_residual {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) {P : Fin 2 → Subgroup X}
    (hres : ResidualOvergroupsAt X S P) {Q : Fin 2 → Subgroup X}
    (hQS : ∀ i, Subgroup.normalizer (S : Set X) ≤ Q i) (hQtop : ∀ i, Q i ≠ ⊤)
    (hQsolv : ∀ i, ¬ Group.IsSolvable ↥(Q i)) (hQne : dInf (Q 0) ≠ dInf (Q 1))
    {Pst : Subgroup X} (hPS : Subgroup.normalizer (S : Set X) ≤ Pst)
    (hPmax : IsMaxParabolic2 ⊤ Pst) : ∃ i, dInf Pst = dInf (Q i) := by
  obtain ⟨-, -, hcoat, -, hres5, -⟩ := hres
  have hSN : S ≤ Subgroup.normalizer (S : Set X) := Subgroup.le_normalizer
  obtain ⟨M, hM, hPM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom Pst).resolve_left hPmax.2.1
  obtain ⟨j, rfl⟩ := (hcoat M ((hSN.trans hPS).trans hPM)).mp hM.covBy_top
  have hpar : IsParabolic2 ⊤ (P j) :=
    ⟨le_top, S, hS, fun x hx => hPM (hPS hx.2)⟩
  have hPj : P j = Pst := hPmax.2.2 (P j) hpar hM.1 hPM
  have hk : ∀ i, ∃ k, dInf (Q i) = dInf (P k) := fun i => by
    obtain ⟨k, -, hk⟩ := hres5 (Q i) (hSN.trans (hQS i)) (hQtop i) (hQsolv i)
    exact ⟨k, hk⟩
  obtain ⟨k₀, hk₀⟩ := hk 0
  obtain ⟨k₁, hk₁⟩ := hk 1
  have hne : k₀ ≠ k₁ := fun h => hQne (by rw [hk₀, hk₁, h])
  rw [← hPj]
  have : j = k₀ ∨ j = k₁ := by omega
  rcases this with rfl | rfl
  · exact ⟨0, hk₀.symm⟩
  · exact ⟨1, hk₁.symm⟩

end Residual

section Quotient

variable {A B : Type} [Group A] [Group B] {f : A →* B}

theorem mem_of_two_pow_of_mem_sup (hker : f.ker ≤ Subgroup.center A) (hodd : Odd (Nat.card f.ker))
    {S : Subgroup A} (hS : IsPGroup 2 ↥S) {x : A} (hx : x ∈ S ⊔ f.ker) {e : ℕ}
    (he : x ^ 2 ^ e = 1) : x ∈ S := by
  have hnorm : (f.ker).Normal := f.normal_ker
  obtain ⟨s, hs, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  have hkc : ∀ y, k * y = y * k := fun y => (Subgroup.mem_center_iff.mp (hker hk) y).symm
  have hsk : Commute s k := (hkc s).symm
  have hpow : (s * k) ^ 2 ^ e = s ^ 2 ^ e * k ^ 2 ^ e := hsk.mul_pow _
  obtain ⟨m, hm⟩ := hS ⟨s, hs⟩
  have hm' : s ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hk1 : k ^ 2 ^ (e + m) = 1 := by
    have h1 : (s ^ 2 ^ e * k ^ 2 ^ e) ^ 2 ^ m = 1 := by rw [← hpow, he, one_pow]
    rw [(hsk.pow_pow _ _).mul_pow] at h1
    have hs1 : (s ^ 2 ^ e) ^ 2 ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hm', one_pow]
    rw [hs1, one_mul, ← pow_mul, ← pow_add] at h1
    exact h1
  have hk2 : (⟨k, hk⟩ : ↥f.ker) ^ 2 ^ (e + m) = 1 := Subtype.ext hk1
  have hord : orderOf (⟨k, hk⟩ : ↥f.ker) ∣ Nat.card ↥f.ker := orderOf_dvd_natCard _
  have hord2 : orderOf (⟨k, hk⟩ : ↥f.ker) ∣ 2 ^ (e + m) := orderOf_dvd_of_pow_eq_one hk2
  have hcop : Nat.Coprime (Nat.card ↥f.ker) (2 ^ (e + m)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  have h1 : orderOf (⟨k, hk⟩ : ↥f.ker) = 1 := Nat.eq_one_of_dvd_coprimes hcop hord hord2
  have hk3 : k = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
  rw [hk3, mul_one]
  exact hs

theorem mem_normalizer_of_map (hker : f.ker ≤ Subgroup.center A) (hodd : Odd (Nat.card f.ker))
    {S : Subgroup A} (hS : IsPGroup 2 ↥S) {a : A}
    (ha : f a ∈ Subgroup.normalizer ((S.map f : Subgroup B) : Set B)) :
    a ∈ Subgroup.normalizer (S : Set A) := by
  have key : ∀ b : A, f b ∈ Subgroup.normalizer ((S.map f : Subgroup B) : Set B) →
      ∀ s ∈ S, b * s * b⁻¹ ∈ S := by
    intro b hb s hs
    have h1 : f (b * s * b⁻¹) ∈ S.map f := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hb (f s)).mp ⟨s, hs, rfl⟩
    have h2 : b * s * b⁻¹ ∈ S ⊔ f.ker := by
      rw [← Subgroup.comap_map_eq]
      exact h1
    obtain ⟨e, he⟩ := hS ⟨s, hs⟩
    have he' : s ^ 2 ^ e = 1 := congrArg Subtype.val he
    refine mem_of_two_pow_of_mem_sup hker hodd hS h2 (e := e) ?_
    rw [conj_pow, he', mul_one, mul_inv_cancel]
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨key a ha s, fun hs => ?_⟩
  have ha' : f a⁻¹ ∈ Subgroup.normalizer ((S.map f : Subgroup B) : Set B) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ ha
  have := key a⁻¹ ha' _ hs
  simpa [mul_assoc] using this

theorem isMaxParabolic2_map (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center A)
    (hodd : Odd (Nat.card f.ker)) {P : Subgroup A} (hP : IsMaxParabolic2 ⊤ P) :
    IsMaxParabolic2 ⊤ (P.map f) := by
  obtain ⟨⟨-, S, hS, hNS⟩, hne, hmax⟩ := hP
  obtain ⟨-, hS2, hSi⟩ := hS
  have hcenN : Subgroup.center A ≤ Subgroup.normalizer (S : Set A) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro s
    rw [(Subgroup.mem_center_iff.mp hz s).symm, mul_inv_cancel_right]
  have hkerP : f.ker ≤ P := fun k hk => hNS ⟨Subgroup.mem_top k, hcenN (hker hk)⟩
  have hmapS : S.map f = (S ⊔ f.ker).map f := by
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq]
  have hS' : IsSylowTwoOf (S.map f) ⊤ := by
    refine ⟨le_top, hS2.map f, ?_⟩
    rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at hSi
    rw [show ((S.map f).subgroupOf ⊤).index = (S.map f).index from
      Subgroup.relIndex_top_right _, hmapS, Subgroup.index_map_eq _ hf le_sup_right]
    exact fun h => hSi (h.trans (Subgroup.index_dvd_of_le le_sup_left))
  have hN : ⊤ ⊓ Subgroup.normalizer ((S.map f : Subgroup B) : Set B) ≤ P.map f := by
    rintro x ⟨-, hx⟩
    obtain ⟨a, rfl⟩ := hf x
    exact ⟨a, hNS ⟨Subgroup.mem_top a, mem_normalizer_of_map hker hodd hS2 hx⟩, rfl⟩
  have hpar : IsParabolic2 ⊤ (P.map f) := ⟨le_top, S.map f, hS', hN⟩
  refine ⟨hpar, fun htop => hne ?_, fun Q hQ hQne hPQ => ?_⟩
  · rw [eq_top_iff]
    intro a _
    obtain ⟨p, hp, hpa⟩ := (htop.symm ▸ Subgroup.mem_top (f a) : f a ∈ P.map f)
    have hk : p⁻¹ * a ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpa, inv_mul_cancel]
    have := P.mul_mem hp (hkerP hk)
    rwa [mul_inv_cancel_left] at this
  · have hPQ' : P ≤ Q.comap f := Subgroup.map_le_iff_le_comap.mp hPQ
    have hpar' : IsParabolic2 ⊤ (Q.comap f) :=
      ⟨le_top, S, ⟨le_top, hS2, hSi⟩, hNS.trans hPQ'⟩
    have hne' : Q.comap f ≠ ⊤ := fun h => hQne (by
      rw [← Subgroup.map_comap_eq_self_of_surjective hf Q, h, Subgroup.map_top_of_surjective f hf])
    have := hmax (Q.comap f) hpar' hne' hPQ'
    rw [← this, Subgroup.map_comap_eq_self_of_surjective hf Q]

end Quotient

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
