module

public import CFSG.Quasithin.Background.S1549DL3G
public import CFSG.Quasithin.Background.S1549DL3N
public import CFSG.Quasithin.Background.InternalSecB5
public import CFSG.Quasithin.Background.C1PackS15348

public section

namespace CFSG.Quasithin

namespace S1549D

open CFSG.QuasithinUnique CFSG.Open CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V]

omit [CommGroup V] in
theorem pCoreOf_le_pCoreOf_of_normalizes {Ω : Type} [Group Ω] [Finite Ω] {N X : Subgroup Ω}
    (hNX : N ≤ X) (hn : X ≤ Subgroup.normalizer (N : Set Ω)) : pCoreOf 2 N ≤ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRX : pCoreOf 2 N ≤ X := (pCoreOf_le 2 N).trans hNX
  refine le_pCoreOf_of_le_normalizer 2 hRX ?_ (pCoreOf_isPGroup 2 N)
  intro x hx
  have h1 : conjSub x N = N := B6.conjSub_eq_self (hn hx)
  have h2 : conjSub x (pCoreOf 2 N) = pCoreOf 2 N := by
    rw [← pCoreOf_conjSub, h1]
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    rw [← h2]
    exact mul_mem_conjSub hr
  · intro hr
    rw [← h2] at hr
    have := mem_conjSub.mp hr
    simpa [mul_assoc] using this

section Inv

variable {L X : Subgroup (MulAut V)}

theorem le_normalizer_of_conj {L X : Subgroup (MulAut V)} (hLn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) :
    X ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨fun hl => hLn x hx l hl, fun h => ?_⟩
  have := hLn x⁻¹ (X.inv_mem hx) _ h
  simpa [mul_assoc] using this

theorem commV_invariant (hLn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) {x : MulAut V} (hx : x ∈ X)
    {u : V} (hu : u ∈ commV L) : x u ∈ commV L := by
  have hle : commV L ≤ (commV L).comap (x : V ≃* V).toMonoidHom := by
    unfold commV
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, v, rfl⟩
    show x (l v * v⁻¹) ∈ commV L
    have e : x (l v * v⁻¹) = (x * l * x⁻¹) (x v) * (x v)⁻¹ := by
      simp
    rw [e]
    exact Subgroup.subset_closure ⟨_, hLn x hx l hl, x v, rfl⟩
  exact hle hu

theorem fixV_invariant (hLn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) {x : MulAut V} (hx : x ∈ X)
    {c : V} (hc : c ∈ fixV L) : x c ∈ fixV L := by
  intro l hl
  have h1 : x⁻¹ * l * x⁻¹⁻¹ ∈ L := hLn x⁻¹ (X.inv_mem hx) l hl
  have h2 := hc _ h1
  have e : l (x c) = x ((x⁻¹ * l * x⁻¹⁻¹) c) := by simp
  rw [e, h2]

end Inv

variable [Finite V]

theorem l3_endgame
    (hB51 : AsB51) (hV : ∀ v : V, v ^ 2 = 1)
    {X L S P₀ M' A : Subgroup (MulAut V)}
    (hLX : L ≤ X) (hLn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hLq : CFSG.IsQuasisimple ↥L) (hLs : SQTKGroup ↥L) (hLc : Nat.card ↥L = 168)
    (hS : IsSylowTwoOf S X) (hXLS : X ≤ L ⊔ S) (hO2 : pCoreOf 2 X = ⊥)
    (hLJ : L ≤ ffJ X) (hA : IsStrongFFStarOffender X A)
    {z : V} (hzS : ∀ s ∈ S, s z = z)
    (hgen : Subgroup.closure {v : V | ∃ g ∈ X, g z = v} = ⊤)
    (hM : ∀ g ∈ X, g z = z → g ∈ M')
    (hP₀L : P₀ ≤ L) (hpar : IsMinParabolicOf L P₀) (hSL : S ⊓ L ≤ P₀)
    (hPM : P₀ ⊔ S ≤ M') (hAP : A ≤ pCoreOf 2 (P₀ ⊔ S)) : L ≤ M' := by
  classical
  have hXn : X ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_conj hLn
  have hX2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ L := fun x hx =>
    C1Pack153.exists_pow_mem_of_mem_sup_two hS.2.1 (fun s hs => hXn (hS.1 hs)) (hXLS hx)
  set G₁ := ffJ X with hG₁
  have hG₁X : G₁ ≤ X := B6.ffJ_le X
  have hLo := B1Red.isQuasisimple_to_open hLq
  have hG₁n : ∀ y ∈ G₁, ∀ l ∈ L, y * l * y⁻¹ ∈ L := fun y hy l hl => hLn y (hG₁X hy) l hl
  have hG₁2 : ∀ y ∈ G₁, ∃ e : ℕ, y ^ 2 ^ e ∈ L := fun y hy => hX2 y (hG₁X hy)
  have hO2G₁ : pCoreOf 2 G₁ = ⊥ := by
    refine le_bot_iff.mp ?_
    have h1 := pCoreOf_le_pCoreOf_of_normalizes hG₁X (B6.le_normalizer_ffJ X)
    rwa [hO2] at h1
  have hFstar : quasithinGenFitting G₁ = L :=
    InternalSec.quasithinGenFitting_eq_of_two_pow hLJ hG₁n hLo hG₁2 hO2G₁
  have hB : B51Hyp G₁ L := by
    refine ⟨?_, hLq, hLs, hLJ, hO2G₁, (InternalSec.ffJ_ffJ X).symm⟩
    have hZL : centerOf G₁ ≤ L := (FFC.centerOf_le_genFitting G₁).trans hFstar.le
    rw [hFstar, sup_eq_left.mpr hZL]
  have hq := l3_natural_or_q_one hB51 hV hB hLc
  have hAoff := hA.1
  have hAG₁ : A ≤ G₁ := B6.le_ffJ hAoff
  rcases hq with hq | hnat
  · exfalso
    have hA' : IsFFStarOffender G₁ A := ⟨hAG₁, hAoff.2⟩
    have h1 := rAV_eq_one_of_one_le_qOf hV hq hA'
    have h2 := hA.2
    rw [h1] at h2
    exact lt_irrefl _ h2
  obtain ⟨D⟩ := hnat.toL3Coord
  have hZL : ∀ l ∈ L, ∀ z ∈ fixV L ⊓ commV L, l z = z := fun l hl z hz => hz.1 l hl
  have hXU : ∀ x ∈ X, ∀ u ∈ commV L, x u ∈ commV L := fun x hx u hu => commV_invariant hLn hx hu
  have hXZ : ∀ x ∈ X, ∀ z ∈ fixV L ⊓ commV L, x z ∈ fixV L ⊓ commV L := fun x hx z hz =>
    ⟨fixV_invariant hLn hx hz.1, commV_invariant hLn hx hz.2⟩
  have hXleL : X ≤ L := le_of_two_quotient D hZL hLX hXU hXZ hX2 hO2
  have hXL : X = L := le_antisymm hXleL hLX
  have hSL' : IsSylowTwoOf S L := hXL ▸ hS
  have hSsubL : S ≤ L := hSL'.1
  have hSP₀ : S ≤ P₀ := fun s hs => hSL ⟨hs, hSsubL hs⟩
  have hP₀S : P₀ ⊔ S = P₀ := sup_eq_left.mpr hSP₀
  obtain ⟨T', hT', hP⟩ := hpar
  have hT'P : T' < P₀ := hP.1.2.1
  have hnormT' : ¬ P₀ ≤ Subgroup.normalizer (T' : Set (MulAut V)) := hP.2
  have hSylS : IsSylowTwoOf S P₀ := isSylowTwoOf_of_le' hSL' hSP₀ hP₀L
  have hSylT : IsSylowTwoOf T' P₀ := isSylowTwoOf_of_le' hT' hT'P.le hP₀L
  obtain ⟨h, hh, hconj⟩ := hSylS.exists_conj hSylT
  have hconj' : T' = conjSub h S := hconj
  have hSne : S ≠ P₀ := by
    intro hSeq
    have : conjSub h S = S := by
      rw [hSeq]
      exact B6.conjSub_eq_self (Subgroup.le_normalizer hh)
    rw [this, hSeq] at hconj'
    exact hT'P.ne hconj'
  have hSn : ¬ P₀ ≤ Subgroup.normalizer (S : Set (MulAut V)) := by
    intro hn
    have : conjSub h S = S := B6.conjSub_eq_self (hn hh)
    rw [this] at hconj'
    exact hnormT' (hconj' ▸ hn)
  have hst : rkIdx (fixV A) < rk A := by
    have h1 := (rAV_lt_one_iff hV hAoff.isA2).mp hA.2
    exact (B1.card_lt_iff hV hAoff.2.2.1).mp h1
  have hAL : A ≤ L := hAG₁.trans (hG₁X.trans hXleL)
  have hAP' : A ≤ pCoreOf 2 P₀ := by rwa [hP₀S] at hAP
  rw [hXL] at hgen
  have htop : commV L ⊔ fixV L = ⊤ := commV_sup_fixV_eq_top hV hSL' hzS hgen
  obtain ⟨u, hu, c, hc, huc⟩ := Subgroup.mem_sup.mp (htop ▸ Subgroup.mem_top z)
  have hSu : ∀ s ∈ S, s u = u := by
    intro s hs
    have h1 : s (u * c) = u * c := by rw [huc]; exact hzS s hs
    rw [map_mul, hc s (hSsubL hs)] at h1
    exact mul_right_cancel h1
  have hu0 : D.β ⟨u, hu⟩ ≠ 1 := by
    intro h1
    have huZ : u ∈ fixV L ⊓ commV L := (D.ker_β ⟨u, hu⟩).mp h1
    have hzfix : z ∈ fixV L := by
      rw [← huc]
      exact Subgroup.mul_mem _ huZ.1 hc
    have hfix : fixV L = ⊤ := by
      refine eq_top_iff.mpr ?_
      rw [← hgen, Subgroup.closure_le]
      rintro _ ⟨g, hg, rfl⟩
      rw [hzfix g hg]
      exact hzfix
    have hL1 : L ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hLc
      omega
    obtain ⟨l, hl⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hL1
    apply hl
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    exact (hfix ▸ Subgroup.mem_top v : v ∈ fixV L) l l.2
  have hM' : ∀ g ∈ L, g (u * c) = u * c → g ∈ M' := by
    intro g hg hgz
    rw [huc] at hgz
    exact hM g (hLX hg) hgz
  exact l3_geometry hV D hZL hSL' hP₀L hSP₀ hSne hSn (le_sup_left.trans hPM) hAoff.2.2.1 hAoff.2.1
    hAL hAP' hst hu (hu0) hSu hc hM'

end S1549D

end CFSG.Quasithin
