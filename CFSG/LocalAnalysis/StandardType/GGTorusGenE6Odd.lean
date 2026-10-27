module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Comm
public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Cover
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHolds

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

private lemma commutator_mul_central {G : Type*} [Group G] {z x y : G}
    (hz : z ∈ Subgroup.center G) :
    x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have hzx : z * x⁻¹ = x⁻¹ * z := (Subgroup.mem_center_iff.1 hz x⁻¹).symm
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹
      = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [hzx]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem strong_odd_of_good {R : Type} [Group R] [Finite R] {L' : Type} [Group L'] [Finite L']
    (D : FrameData R) (hAL : GGAbelianLift) (hD : D.Good) (hRG : GGE6ThreeRGen D)
    {I : Set (MulAut R)} (hM4 : GGE6ThreeCoverCommSCr R I)
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) (hcard : Nat.card ψ.ker = 1 ∨ Nat.card ψ.ker = 3)
    {ρ : MulAut L' →* MulAut R} (hρ : ∀ a l, ρ a (ψ l) = ψ (a l)) (hρinj : Function.Injective ρ)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A) (hsc : GGTorusSelfCent 3 A)
    (hal : ∀ a ∈ A, ρ a ∈ D.diag.range) (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l))
    (h5 : 3 ^ 5 ≤ Nat.card A) : GGE6ThreeStrongData ψ.ker A := by
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) (fun f g h => by
      ext x; exact congrFun h x)
  have hodd : Odd (Nat.card ψ.ker) := by
    rcases hcard with h | h <;> rw [h] <;> decide
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g.1 g.2)⟩
  choose w hw hw2 using fun i => exists_weyl_lift_odd D hD.weyl hψ hker hodd i
  let e : Multiplicative (Fin Tag.E6.rank → ZMod 3) ≃* D.diag.range :=
    MonoidHom.ofInjective hD.faithful
  let ρA : A →* D.diag.range := (ρ.comp A.subtype).codRestrict D.diag.range fun a => hal a a.2
  let Φ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3) := e.symm.toMonoidHom.comp ρA
  have hΦ : ∀ a : A, D.diag (Φ a) = ρ a := fun a =>
    congrArg Subtype.val (e.apply_symm_apply (ρA a))
  have hinj : Function.Injective Φ := by
    intro a b hab
    apply Subtype.ext
    apply hρinj
    rw [← hΦ a, ← hΦ b, hab]
  obtain ⟨hTab, hTfix, -⟩ := abelianLift_apply D hAL hD hψ hker hcard hρ hAp hal hw
  have hinner := innerPoints_realized D hAL hD hψ hker hcard hρ hA hsc hal hw
  have hinner' : ∀ v ∈ NoOffRest.hypE6, ∃ a ∈ A, ρ a = D.ad v := by
    intro v hv
    obtain ⟨t, -, -, -, a, ha, -, hρa⟩ := hinner v hv
    exact ⟨a, ha, hρa⟩
  have hrange := range_clause D hD.faithful hΦ hinner'
  have htmax : ∀ c : L', (∀ a ∈ A, a c = c) → Odd (orderOf c) → c ∈ D.Tor.comap ψ := by
    intro c hc _
    rw [Subgroup.mem_comap]
    refine (hD.cent (ψ c)).1 fun v hv => ?_
    obtain ⟨b, hb, hbρ⟩ := hinner' v hv
    rw [← hbρ, hρ b c, hc b hb]
  refine ⟨D.Tor.comap ψ, w, hTab, ?_, hTfix, ?_, htmax, ?_⟩
  · intro z hz _
    show ψ z ∈ D.Tor
    rw [(MonoidHom.mem_ker).1 hz]
    exact D.Tor.one_mem
  · exact coboundary_clause D hAL hD hψ hker hcard hρ hAp hal hw
  ·
    intro a ha hane J hJ c hcT hc3
    have hΦ_ne : Φ ⟨a, ha⟩ ≠ 1 := by
      intro h1
      apply hane
      have hsub : (⟨a, ha⟩ : A) = 1 := by
        apply hinj
        rw [h1, map_one]
      exact Subtype.ext_iff.mp hsub
    set x : Fin Tag.E6.rank → ZMod 3 := Multiplicative.toAdd (Φ ⟨a, ha⟩) with hxdef
    have hx : x ≠ 0 := by
      intro h0
      apply hΦ_ne
      have h2 : Multiplicative.ofAdd x = 1 := by rw [h0]; rfl
      simpa [hxdef] using h2
    have hρa : D.ad x = ρ a := by
      have h := hΦ ⟨a, ha⟩
      simpa [FrameData.ad, hxdef] using h
    have hab : ∀ l : L', D.ad x (ψ l) = ψ (a l) := by
      intro l
      rw [hρa]
      exact hρ a l
    have hK : IsComponentOf (J.map ψ) (ggFix (D.ad x)) :=
      isComponentOf_map_ggFix_of_central hψ hker hab hJ
    have hψcT : ψ c ∈ D.Tor := hcT
    have hψc3 : ∃ k : ℕ, (ψ c) ^ 3 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hc3
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    have hrg := hRG x hx (J.map ψ) hK (ψ c) hψcT hψc3
    have key : ∀ n ∈ Subgroup.closure (Set.range w),
        (∀ t ∈ D.Tor.comap ψ, n * t * n⁻¹ ∈ D.Tor.comap ψ) ∧
        (∀ t ∈ D.Tor.comap ψ, n⁻¹ * t * n ∈ D.Tor.comap ψ) := by
      intro n hn
      refine Subgroup.closure_induction (p := fun n _ =>
        (∀ t ∈ D.Tor.comap ψ, n * t * n⁻¹ ∈ D.Tor.comap ψ) ∧
        (∀ t ∈ D.Tor.comap ψ, n⁻¹ * t * n ∈ D.Tor.comap ψ)) ?_ ?_ ?_ ?_ hn
      · rintro _ ⟨i, rfl⟩
        have hnb : (D.nb i)⁻¹ = D.nb i := inv_eq_of_mul_eq_one_right (hD.weyl.1 i)
        constructor
        · intro t ht
          rw [Subgroup.mem_comap] at ht ⊢
          rw [map_mul, map_mul, map_inv, hw i]
          exact hD.weyl.2.1 i (ψ t) ht
        · intro t ht
          rw [Subgroup.mem_comap] at ht ⊢
          rw [map_mul, map_mul, map_inv, hw i]
          simpa [hnb] using hD.weyl.2.1 i (ψ t) ht
      · constructor <;> intro t ht <;> simpa using ht
      · rintro x y _ _ ⟨px, px'⟩ ⟨py, py'⟩
        constructor
        · intro t ht
          have h1 : y * t * y⁻¹ ∈ D.Tor.comap ψ := py t ht
          have h2 : x * (y * t * y⁻¹) * x⁻¹ ∈ D.Tor.comap ψ := px (y * t * y⁻¹) h1
          rwa [show x * (y * t * y⁻¹) * x⁻¹ = (x * y) * t * (x * y)⁻¹ from by group] at h2
        · intro t ht
          have h1 : x⁻¹ * t * x ∈ D.Tor.comap ψ := px' t ht
          have h2 : y⁻¹ * (x⁻¹ * t * x) * y ∈ D.Tor.comap ψ := py' (x⁻¹ * t * x) h1
          rwa [show y⁻¹ * (x⁻¹ * t * x) * y = (x * y)⁻¹ * t * (x * y) from by group] at h2
      · rintro n _ ⟨pn, pn'⟩
        refine ⟨?_, ?_⟩
        · intro t ht
          simpa using pn' t ht
        · intro t ht
          simpa using pn t ht
    have hTnorm : ∀ n ∈ Subgroup.closure (Set.range w), ∀ t ∈ D.Tor.comap ψ,
        n * t * n⁻¹ ∈ D.Tor.comap ψ := fun n hn => (key n hn).1
    set gen : Set L' := ⋃ n ∈ (Subgroup.closure (Set.range w) : Set L'),
      (fun s => n * s * n⁻¹) '' {s : L' | s ∈ J ∧ s ∈ D.Tor.comap ψ ∧ ∃ k : ℕ, s ^ 3 ^ k = 1}
      with hgendef
    set G : Subgroup L' := Subgroup.closure gen with hGdef
    have hG_le_T : G ≤ D.Tor.comap ψ := by
      rw [hGdef]
      apply (Subgroup.closure_le (D.Tor.comap ψ)).2
      intro y hy
      rw [hgendef] at hy
      rw [Set.mem_iUnion₂] at hy
      obtain ⟨m, hm, s, hs, rfl⟩ := hy
      exact hTnorm m hm s hs.2.1
    have hgen_inv : ∀ n ∈ Subgroup.closure (Set.range w), ∀ y ∈ gen, n * y * n⁻¹ ∈ gen := by
      intro n hn y hy
      rw [hgendef] at hy
      rw [Set.mem_iUnion₂] at hy
      obtain ⟨m, hm, s, hs, rfl⟩ := hy
      rw [hgendef]
      exact Set.mem_iUnion₂.mpr ⟨n * m, Subgroup.mul_mem _ hn hm, s, hs, by group⟩
    have hG_inv : ∀ n ∈ Subgroup.closure (Set.range w), ∀ g ∈ G, n * g * n⁻¹ ∈ G := by
      intro n hn g hg
      rw [hGdef] at hg ⊢
      refine Subgroup.closure_induction (p := fun g _ => n * g * n⁻¹ ∈ Subgroup.closure gen)
        ?_ ?_ ?_ ?_ hg
      · intro y hy
        exact Subgroup.subset_closure (hgen_inv n hn y hy)
      · simpa using Subgroup.one_mem (Subgroup.closure gen)
      · intro x y _ _ hx hy
        rw [show n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) from by group]
        exact Subgroup.mul_mem _ hx hy
      · intro x _ hx
        rw [show n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ from by group]
        exact Subgroup.inv_mem _ hx
    have hle : (Subgroup.closure (⋃ n ∈ (Subgroup.closure (Set.range D.nb) : Set R),
        (fun s => n * s * n⁻¹) '' {s : R | s ∈ J.map ψ ∧ s ∈ D.Tor ∧ ∃ k : ℕ, s ^ 3 ^ k = 1}))
        ≤ G.map ψ := by
      apply (Subgroup.closure_le (G.map ψ)).2
      intro y hy
      rw [Set.mem_iUnion₂] at hy
      obtain ⟨n, hn, s, hs, rfl⟩ := hy
      obtain ⟨n', hn'mem, hn'eq⟩ : ∃ n' ∈ Subgroup.closure (Set.range w), ψ n' = n := by
        have hsub : Set.range D.nb ⊆ (Subgroup.closure (Set.range w)).map ψ := by
          rintro _ ⟨i, rfl⟩
          rw [← hw i]
          exact Subgroup.mem_map_of_mem ψ (Subgroup.subset_closure (show w i ∈ Set.range w from ⟨i, rfl⟩))
        exact (Subgroup.closure_le _).2 hsub hn
      obtain ⟨j, hjJ, hjψ⟩ : ∃ j ∈ J, ψ j = s := Subgroup.mem_map.1 hs.1
      have hjT : j ∈ D.Tor.comap ψ := by
        rw [Subgroup.mem_comap, hjψ]; exact hs.2.1
      obtain ⟨k, hsk⟩ := hs.2.2
      have hj3 : j ^ 3 ^ (k + 1) = 1 := by
        have hmem : j ^ 3 ^ k ∈ ψ.ker := by
          rw [MonoidHom.mem_ker, map_pow, hjψ, hsk]
        have h1 : (⟨j ^ 3 ^ k, hmem⟩ : ψ.ker) ^ Nat.card ψ.ker = 1 := pow_card_eq_one'
        have h2 : j ^ (3 ^ k * Nat.card ψ.ker) = 1 := by
          have := congrArg Subtype.val h1
          simpa [pow_mul] using this
        have hdiv : 3 ^ k * Nat.card ψ.ker ∣ 3 ^ (k + 1) := by
          rcases hcard with h | h
          · rw [h, mul_one]; exact pow_dvd_pow 3 (Nat.le_succ k)
          · rw [h, pow_succ]
        obtain ⟨d, hd⟩ := hdiv
        rw [hd, pow_mul, h2, one_pow]
      refine ⟨n' * j * n'⁻¹, ?_, ?_⟩
      · refine Subgroup.subset_closure ?_
        exact Set.mem_iUnion₂.mpr ⟨n', hn'mem, j, ⟨hjJ, hjT, ⟨k + 1, hj3⟩⟩, rfl⟩
      · rw [map_mul, map_mul, map_inv, hn'eq, hjψ]
    have hmapG_of : ∀ c' : L', c' ∈ D.Tor.comap ψ → (∃ k : ℕ, c' ^ 3 ^ k = 1) →
        ψ c' ∈ G.map ψ := by
      intro c' hc'T hc'3
      refine hle (hRG x hx (J.map ψ) hK (ψ c') hc'T ?_)
      obtain ⟨k, hk⟩ := hc'3
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    have hψcG : ψ c ∈ G.map ψ := hmapG_of c hcT hc3
    obtain ⟨g, hgG, hgψ⟩ := Subgroup.mem_map.1 hψcG
    have hzker : g⁻¹ * c ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hgψ, inv_mul_cancel]
    have hz3 : ∃ k : ℕ, (g⁻¹ * c) ^ 3 ^ k = 1 := by
      have h2 : (g⁻¹ * c) ^ Nat.card ψ.ker = 1 := by
        have h1 : (⟨g⁻¹ * c, hzker⟩ : ψ.ker) ^ Nat.card ψ.ker = 1 := pow_card_eq_one'
        exact congrArg Subtype.val h1
      refine ⟨1, ?_⟩
      rcases hcard with h | h
      · rw [h, pow_one] at h2
        simpa [h2]
      · rw [h] at h2
        simpa using h2
    have hzG : g⁻¹ * c ∈ G := by
      have hm4 := hM4 L' ψ hψ hker hperf A hA hAI h5 hsc (g⁻¹ * c) hzker hz3
      rw [hGdef]
      refine ((Subgroup.closure_le (Subgroup.closure gen)).2 ?_) hm4
      rintro _ ⟨m, t, hmn, htf, ht3, rfl⟩
      have hnorm : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        have hmap_le : A.map (MulAut.conj (MulAut.conj m)).toMonoidHom ≤ A := by
          rintro _ ⟨a', ha', rfl⟩
          simpa [MulAut.conj_apply] using hmn a' ha'
        exact Subgroup.eq_of_le_of_card_ge hmap_le
          (le_of_eq (Subgroup.card_map_of_injective
            (MulAut.conj (MulAut.conj m)).injective).symm)
      obtain ⟨v, hv, hvt⟩ := normalizer_clause D hD hψ hρ hΦ hrange hw m hnorm
      have htodd : Odd (orderOf t) :=
        (show Odd 3 by decide).of_dvd_nat (orderOf_dvd_of_pow_eq_one ht3)
      have htT : t ∈ D.Tor.comap ψ := htmax t htf htodd
      have htpow : ∃ k : ℕ, t ^ 3 ^ k = 1 := ⟨1, by simpa using ht3⟩
      have hψtG : ψ t ∈ G.map ψ := hmapG_of t htT htpow
      obtain ⟨g', hg'G, hg'ψ⟩ := Subgroup.mem_map.1 hψtG
      have hz'ker : g'⁻¹ * t ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hg'ψ, inv_mul_cancel]
      have hz'cen : g'⁻¹ * t ∈ Subgroup.center L' := hker hz'ker
      have hv_g'_G : v * g' * v⁻¹ ∈ G := hG_inv v hv g' hg'G
      have hv_g'_T : v * g' * v⁻¹ ∈ D.Tor.comap ψ := hG_le_T hv_g'_G
      have ht0T : m * v⁻¹ ∈ D.Tor.comap ψ := hvt
      have hcomm : (m * v⁻¹) * (v * g' * v⁻¹) * (m * v⁻¹)⁻¹ = v * g' * v⁻¹ := by
        rw [hTab (m * v⁻¹) ht0T (v * g' * v⁻¹) hv_g'_T, mul_assoc, mul_inv_cancel, mul_one]
      have hcommut : m * t * m⁻¹ * t⁻¹ = (v * g' * v⁻¹) * g'⁻¹ := by
        calc m * t * m⁻¹ * t⁻¹
            = m * (g' * (g'⁻¹ * t)) * m⁻¹ * (g' * (g'⁻¹ * t))⁻¹ := by
                rw [show g' * (g'⁻¹ * t) = t from by group]
          _ = m * g' * m⁻¹ * g'⁻¹ := commutator_mul_central (z := g'⁻¹ * t) hz'cen
          _ = (m * v⁻¹) * v * g' * v⁻¹ * (m * v⁻¹)⁻¹ * g'⁻¹ := by
                rw [show m = (m * v⁻¹) * v from by group]; group
          _ = (m * v⁻¹) * (v * g' * v⁻¹) * (m * v⁻¹)⁻¹ * g'⁻¹ := by group
          _ = (v * g' * v⁻¹) * g'⁻¹ := by rw [hcomm]
      rw [hcommut]
      exact G.mul_mem hv_g'_G (G.inv_mem hg'G)
    have : c = g * (g⁻¹ * c) := by group
    rw [this]
    exact G.mul_mem hgG hzG

end CFSG.StandardType.E6ThreeModel

end
