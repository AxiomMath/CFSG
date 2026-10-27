module

public import CFSG.CharacterTheory.PSL2Table.Tori
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch3E213MP3B
public import CFSG.Quasithin.Vol2.GoldschmidtE217Klein
public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Rigid

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M E217R3
open CFSG.GorensteinWalter (PSL2)

namespace E217R4

theorem mem_sup_of_central_involution
    {Y : Type} [Group Y] [Finite Y] {F : Type} [Field F] [Finite F] {p : ℕ}
    {K₁ K₂ S : Subgroup Y} {t v : Y} (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7)
    (hF : Nat.card F = p) (θ : K₁ ≃* PSL2 F) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hd : K₁ ⊓ K₂ = ⊥) (hKn : (K₁ ⊔ K₂).Normal)
    (hCK : ∀ a : Y, (∀ k ∈ K₁ ⊔ K₂, a * k = k * a) → a = 1) (hSsyl : IsSylowTwoOf S ⊤)
    (htS : t ∈ S) (hK₂ : K₁.map (MulAut.conj t).toMonoidHom = K₂) (haut : 8 < E2.autCard S K₁)
    (hv2 : v * v = 1) (hv1 : v ≠ 1) (hvS : ∀ s ∈ S, s * v = v * s) : v ∈ K₁ ⊔ K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := hSsyl.2.1
  obtain ⟨u, hu2, hu1, huN⟩ : ∃ u : Y, u * u = 1 ∧ u ≠ 1 ∧ u ∈ K₁ ⊔ K₂ := by
    set w := CFSG.PSL2Table.splitWeyl F with hw
    have hw1 : w ≠ 1 := fun h' => CFSG.PSL2Table.splitWeyl_not_mem
      (h' ▸ (CFSG.PSL2Table.splitTorus F).one_mem)
    refine ⟨((θ.symm w : ↥K₁) : Y), ?_, ?_, Subgroup.mem_sup_left (θ.symm w).2⟩
    · have : (θ.symm w) * (θ.symm w) = 1 := by
        rw [← map_mul, CFSG.PSL2Table.splitWeyl_mul_self, map_one]
      exact congrArg Subtype.val this
    · intro h'
      apply hw1
      have : θ.symm w = 1 := Subtype.ext h'
      simpa using congrArg θ this
  have hY : S ⊓ (K₁ ⊔ K₂) ≠ ⊥ := by
    have hu2g : IsPGroup 2 (Subgroup.zpowers u) := fun x => ⟨1, Subtype.ext (by
      rcases P3.eq_one_or_eq_of_mem_zpowers hu2 x.2 with h' | h'
      · simp [h']
      · simp [h', pow_two, hu2])⟩
    obtain ⟨S', hS', huS'⟩ := exists_isSylowTwoOf_ge hu2g (le_top : Subgroup.zpowers u ≤ ⊤)
    obtain ⟨g, -, hg⟩ := isSylowTwoOf_exists_conj hSsyl hS'
    have huS : u ∈ B6.conjSub g S := hg ▸ huS' (Subgroup.mem_zpowers u)
    rw [B6.mem_conjSub] at huS
    have hmem : g⁻¹ * u * g ∈ S ⊓ (K₁ ⊔ K₂) :=
      ⟨huS, by simpa using hKn.conj_mem u huN g⁻¹⟩
    refine (Subgroup.ne_bot_iff_exists_ne_one).2 ⟨⟨g⁻¹ * u * g, hmem⟩, fun h' => hu1 ?_⟩
    have h'' : g⁻¹ * u * g = 1 := congrArg Subtype.val h'
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = 1 := by rw [h'']; group
  obtain ⟨z, hzY, hz2o, hzS⟩ := exists_involution_mem_center_of_normal hS2
    (inf_le_left : S ⊓ (K₁ ⊔ K₂) ≤ S)
    (fun t ht y hy => ⟨S.mul_mem (S.mul_mem ht hy.1) (S.inv_mem ht), hKn.conj_mem y hy.2 t⟩) hY
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2o, pow_two] at this
  have hz1 : z ≠ 1 := fun h' => by
    rw [h', orderOf_one] at hz2o
    omega
  suffices hvz : v = z from hvz ▸ hzY.2
  by_contra hne
  have hzv : v * z = z * v := (hvS z hzY.1).symm
  set E : Subgroup Y := Subgroup.closure ({v, z} : Set Y) with hE
  have hSc : ∀ s ∈ S, ∀ x ∈ E, s * x = x * s := fun s hs x hx =>
    commute_closure hv2 hz2 hzv (hvS s hs) (hzS s hs) x hx
  have hSE : S ≤ Subgroup.normalizer (E : Set Y) :=
    (show S ≤ Subgroup.centralizer (E : Set Y) from fun s hs =>
      Subgroup.mem_centralizer_iff.2 fun x hx => (hSc s hs x hx).symm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hE4 : 4 ≤ Nat.card E := four_le_card_closure hv2 hz2 hv1 hz1 hne
  obtain ⟨-, a, haE, haC, hEa⟩ := P3.exists_eq_sup hp hp8 hF θ hc hd hKn hCK hSsyl htS hK₂ hSE
    (closure_comm hv2 hz2 hzv) (closure_sq hv2 hz2 hzv) hE4 haut
  have hA : E ⊓ Subgroup.centralizer (K₁ : Set Y) ≠ ⊥ := by
    intro hA
    rw [hA, sup_bot_eq] at hEa
    have ha2 : a * a = 1 := closure_sq hv2 hz2 hzv a haE
    have hsub : (E : Set Y) ⊆ ({1, a} : Set Y) := by
      intro x hx
      have hx' : x ∈ Subgroup.zpowers a := hEa ▸ hx
      rcases P3.eq_one_or_eq_of_mem_zpowers ha2 hx' with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h3 : ({1, a} : Set Y).ncard ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    have h4 : Nat.card ↥E = (E : Set Y).ncard := Nat.card_coe_set_eq (E : Set Y)
    omega
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA
  have hbE : (b : Y) ∈ E := (Subgroup.mem_inf.1 b.2).1
  have hbC : (b : Y) ∈ Subgroup.centralizer (K₁ : Set Y) := (Subgroup.mem_inf.1 b.2).2
  have hbt : t * b = b * t := hSc t htS b hbE
  have hbK₁ : ∀ k ∈ K₁, k * (b : Y) = (b : Y) * k :=
    fun k hk => Subgroup.mem_centralizer_iff.1 hbC k hk
  have hbK₂ : ∀ k ∈ K₂, k * (b : Y) = (b : Y) * k := fun k hk => by
    rw [← hK₂] at hk
    exact (commute_of_mem_map_conj hbt.symm (fun k hk => (hbK₁ k hk).symm) k hk).symm
  refine hb1 (Subtype.ext ?_)
  show (b : Y) = 1
  refine hCK b fun k hk => ?_
  have hle : K₁ ⊔ K₂ ≤ Subgroup.centralizer ({(b : Y)} : Set Y) :=
    sup_le (fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (hbK₁ k hk))
      (fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (hbK₂ k hk))
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hk)).symm

end E217R4

end CFSG.Quasithin
