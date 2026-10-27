module

public import CFSG.Quasithin.Background.FFC11A
public import CFSG.GroupTheory.BaerSuzuki.Helpers

public section

namespace CFSG.Quasithin

namespace SBc6

section Odd

variable {A : Type} [Group A] [Finite A]

theorem odd_orderOf_of_mem_center {x : A ⧸ CFSG.pCore 2 A}
    (hx : x ∈ Subgroup.center (A ⧸ CFSG.pCore 2 A)) : Odd (orderOf x) := by
  by_contra hne
  have hpos : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  have ha : a ≠ 0 := by
    rintro rfl
    exact hne (by simpa [hab] using hb)
  have hbpos : b ≠ 0 := by
    rintro rfl
    exact (Nat.not_odd_zero hb).elim
  have hbd : b ∣ orderOf x := ⟨2 ^ a, by rw [hab]; ring⟩
  set y : A ⧸ CFSG.pCore 2 A := x ^ b with hy
  have hyord : orderOf y = 2 ^ a := by
    rw [hy, orderOf_pow_of_dvd hbpos hbd, hab, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hbpos)]
  have hycent : y ∈ Subgroup.center (A ⧸ CFSG.pCore 2 A) := Subgroup.pow_mem _ hx b
  have hzle : Subgroup.zpowers y ≤ Subgroup.center (A ⧸ CFSG.pCore 2 A) :=
    (Subgroup.zpowers_le).2 hycent
  have hnorm : (Subgroup.zpowers y).Normal := ⟨fun n hn g => by
    have h := Subgroup.mem_center_iff.mp (hzle hn) g
    rw [h, mul_inv_cancel_right]
    exact hn⟩
  have hp2 : IsPGroup 2 (Subgroup.zpowers y) := by
    refine IsPGroup.of_card (n := a) ?_
    rw [Nat.card_zpowers, hyord]
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 A)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.BaerSuzuki.Helpers.pCore_isPGroup 2
  have hpre : IsPGroup 2 ((Subgroup.zpowers y).comap (QuotientGroup.mk' (CFSG.pCore 2 A))) :=
    hp2.comap_of_ker_isPGroup _ hker
  have hpren : ((Subgroup.zpowers y).comap (QuotientGroup.mk' (CFSG.pCore 2 A))).Normal :=
    hnorm.comap _
  have hle := CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hpren hpre
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective y
  have hgmem : g ∈ (Subgroup.zpowers y).comap (QuotientGroup.mk' (CFSG.pCore 2 A)) := by
    rw [Subgroup.mem_comap]
    exact ⟨1, by simp [← hg]⟩
  have hg1 : (QuotientGroup.mk g : A ⧸ CFSG.pCore 2 A) = 1 :=
    (QuotientGroup.eq_one_iff g).2 (hle hgmem)
  have hy1 : y = 1 := by rw [← hg, hg1]
  rw [hy1, orderOf_one] at hyord
  have : 2 ^ a = 1 := hyord.symm
  exact ha (by simpa using (Nat.pow_eq_one.mp this).resolve_left (by norm_num))

end Odd

section Cover

variable {A H : Type} [Group A] [Finite A] [Group H]

theorem ker_le_pCore_of_cover (ψ : A →* H) (hψ : Function.Surjective ψ)
    (hQ : CFSG.pCore 2 A ≤ ψ.ker) (hqs : CFSG.IsQuasisimple (A ⧸ CFSG.pCore 2 A))
    (hH : ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (H ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K))) :
    ψ.ker ≤ CFSG.pCore 2 A := by
  let f : (A ⧸ CFSG.pCore 2 A) →* H := QuotientGroup.lift (CFSG.pCore 2 A) ψ hQ
  have hfmk : ∀ g : A, f (QuotientGroup.mk g) = ψ g := fun g => rfl
  have hf : Function.Surjective f := by
    intro h
    obtain ⟨g, rfl⟩ := hψ h
    exact ⟨QuotientGroup.mk g, hfmk g⟩
  have hopen : CFSG.Open.IsQuasisimple (A ⧸ CFSG.pCore 2 A) := ⟨hqs.1.1, hqs.2.1⟩
  obtain ⟨n, K, hKf, hKfin, hK, ⟨e⟩⟩ := hH
  have : Nontrivial ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) := B69.nontrivial_statedSL_two
  have hHnt : Nontrivial H := e.symm.injective.nontrivial
  have hker_ne : f.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := exists_pair_ne H
    obtain ⟨u, rfl⟩ := hf a
    obtain ⟨v, rfl⟩ := hf b
    apply hab
    have hu : u ∈ f.ker := by rw [htop]; trivial
    have hv : v ∈ f.ker := by rw [htop]; trivial
    rw [MonoidHom.mem_ker.mp hu, MonoidHom.mem_ker.mp hv]
  have hcent : f.ker ≤ Subgroup.center (A ⧸ CFSG.pCore 2 A) :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hopen f.ker hker_ne
  have hodd : ∀ x ∈ f.ker, Odd (orderOf x) := fun x hx => odd_orderOf_of_mem_center (hcent hx)
  have hinj : Function.Injective f :=
    B69.noOddCoverSL2 (A ⧸ CFSG.pCore 2 A) H hopen f hf hodd ⟨n, K, hKf, hKfin, hK, ⟨e⟩⟩
  intro x hx
  have h1 : f (QuotientGroup.mk x) = 1 := by rw [hfmk]; exact hx
  have h2 : (QuotientGroup.mk x : A ⧸ CFSG.pCore 2 A) = 1 := hinj (by rw [h1, map_one])
  exact (QuotientGroup.eq_one_iff x).1 h2

end Cover

end SBc6

end CFSG.Quasithin
