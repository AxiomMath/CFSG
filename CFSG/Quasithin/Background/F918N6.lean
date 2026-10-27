module

public import CFSG.Quasithin.Background.F918N7
public import CFSG.Quasithin.Background.FFC7C
public import CFSG.Quasithin.Background.B5NonB
public import CFSG.Quasithin.Background.F918P2
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.InternalSecB56
public import CFSG.Quasithin.Background.InternalSecB56M

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement Matrix

section General

variable {Ω : Type} [Group Ω]

theorem n6_le_or_commute {K M J N : Subgroup Ω} (hK : CFSG.IsQuasisimple ↥K) (hKM : K ≤ M)
    (hMJ : M ≤ J) (hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hMn : ∀ j ∈ J, ∀ m ∈ M, j * m * j⁻¹ ∈ M) (hNJ : N ≤ J)
    (hNn : ∀ j ∈ J, ∀ n ∈ N, j * n * j⁻¹ ∈ N) :
    K ≤ N ∨ ∀ k ∈ K, ∀ n ∈ N, k * n = n * k := by
  by_cases hKN : K ≤ N
  · exact Or.inl hKN
  right
  have hKo := B1Red.isQuasisimple_to_open hK
  have h1 : ∀ n ∈ N ⊓ M, ∀ l ∈ K, n * l = l * n :=
    B1Red.commute_of_normal_not_le hKo (fun n hn l hl => hKn n hn.2 l hl)
      (fun l hl n hn => ⟨hNn l (hMJ (hKM hl)) n hn.1,
        M.mul_mem (M.mul_mem (hKM hl) hn.2) (M.inv_mem (hKM hl))⟩)
      (fun h => hKN (h.trans inf_le_left))
  have h2 : ⁅K, N⁆ ≤ N ⊓ M := by
    rw [Subgroup.commutator_le]
    intro k hk n hn
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact N.mul_mem (hNn k (hMJ (hKM hk)) n hn) (N.inv_mem hn)
    · have h3 := hMn n (hNJ hn) k⁻¹ (M.inv_mem (hKM hk))
      have e : ⁅k, n⁆ = k * (n * k⁻¹ * n⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact M.mul_mem (hKM hk) h3
  have : Group.IsPerfect ↥K := hK.1
  have h3 : ⁅⁅K, N⁆, K⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx k hk
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact h1 x (h2 hx) k hk
  have h4 := CFSG.ComponentClassification.Quasisimple.perfect_double_commutator K N h3
  intro k hk n hn
  have h5 : ⁅k, n⁆ ∈ (⊥ : Subgroup Ω) := h4 ▸ Subgroup.commutator_mem_commutator hk hn
  rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h5

theorem n6_le_or_le {K M J G₁ G₂ : Subgroup Ω} (hK : CFSG.IsQuasisimple ↥K) (hKM : K ≤ M)
    (hMJ : M ≤ J) (hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hMn : ∀ j ∈ J, ∀ m ∈ M, j * m * j⁻¹ ∈ M) (hG₁ : G₁ ≤ J) (hG₂ : G₂ ≤ J)
    (hn₁ : ∀ j ∈ J, ∀ g ∈ G₁, j * g * j⁻¹ ∈ G₁) (hn₂ : ∀ j ∈ J, ∀ g ∈ G₂, j * g * j⁻¹ ∈ G₂)
    (hKG : K ≤ G₁ ⊔ G₂) : K ≤ G₁ ∨ K ≤ G₂ := by
  rcases n6_le_or_commute hK hKM hMJ hKn hMn hG₁ hn₁ with h | c₁
  · exact Or.inl h
  rcases n6_le_or_commute hK hKM hMJ hKn hMn hG₂ hn₂ with h | c₂
  · exact Or.inr h
  exfalso
  have hcent : G₁ ⊔ G₂ ≤ Subgroup.centralizer (K : Set Ω) := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · exact Subgroup.mem_centralizer_iff.2 fun k hk => c₁ k hk g hg
    · exact Subgroup.mem_centralizer_iff.2 fun k hk => c₂ k hk g hg
  exact InternalSec.not_commute_of_isQuasisimple hK fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 (hcent (hKG hb)) a ha

theorem n6_genFitting_eq_of_quasisimple {K M J : Subgroup Ω} (hK : CFSG.IsQuasisimple ↥K)
    (hKM : K ≤ M) (hMJ : M ≤ J) (hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hMn : ∀ j ∈ J, ∀ m ∈ M, j * m * j⁻¹ ∈ M)
    (hE : CFSG.IsQuasisimple ↥(quasithinGenFitting J)) : quasithinGenFitting J = K := by
  set E := quasithinGenFitting J with hEdef
  have hKE : K ≤ E := by
    refine le_sup_of_le_right (le_sSup ⟨hKM.trans hMJ, ?_, B1Red.isQuasisimple_to_open hK⟩)
    refine IsSubnormal.step hKM ?_ (IsSubnormal.step hMJ ?_ (IsSubnormal.refl _))
    · exact (Subgroup.normal_subgroupOf_iff hKM).2 fun l y hl hy => hKn y hy l hl
    · exact (Subgroup.normal_subgroupOf_iff hMJ).2 fun l y hl hy => hMn y hy l hl
  have hEJ : E ≤ J := quasithinGenFitting_le J
  have hEo := B1Red.isQuasisimple_to_open hE
  have hEM : E ≤ M := by
    have hnorm : ((M ⊓ E).subgroupOf E).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨hMn (g : Ω) (hEJ g.2) x hx.1, E.mul_mem (E.mul_mem g.2 hx.2) (E.inv_mem g.2)⟩
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hEo
      ((M ⊓ E).subgroupOf E) with hc | htop
    · exfalso
      refine InternalSec.not_commute_of_isQuasisimple hK fun a ha b hb => ?_
      have h1 : (⟨a, hKE ha⟩ : ↥E) ∈ Subgroup.center ↥E :=
        hc (show (⟨a, hKE ha⟩ : ↥E) ∈ (M ⊓ E).subgroupOf E from ⟨hKM ha, hKE ha⟩)
      have h2 := Subgroup.mem_center_iff.mp h1 ⟨b, hKE hb⟩
      exact (congrArg Subtype.val h2).symm
    · intro e he
      have : (⟨e, he⟩ : ↥E) ∈ (M ⊓ E).subgroupOf E := by rw [htop]; trivial
      exact this.1
  have hnorm : (K.subgroupOf E).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hKn g (hEM g.2) k hk
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hEo
    (K.subgroupOf E) with hc | htop
  · exfalso
    refine InternalSec.not_commute_of_isQuasisimple hK fun a ha b hb => ?_
    have h1 : (⟨a, hKE ha⟩ : ↥E) ∈ Subgroup.center ↥E := hc ha
    have h2 := Subgroup.mem_center_iff.mp h1 ⟨b, hKE hb⟩
    exact (congrArg Subtype.val h2).symm
  · refine le_antisymm (fun e he => ?_) hKE
    have : (⟨e, he⟩ : ↥E) ∈ K.subgroupOf E := by rw [htop]; trivial
    exact this

end General

section B56

variable {V : Type} [CommGroup V] [Finite V]

theorem n6_genFitting_eq_of_b56Cases {J K M : Subgroup (MulAut V)} (hK : CFSG.IsQuasisimple ↥K)
    (hKM : K ≤ M) (hMJ : M ≤ J) (hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hMn : ∀ j ∈ J, ∀ m ∈ M, j * m * j⁻¹ ∈ M) (hcomm : commV K = ⊤)
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) :
    quasithinGenFitting J = K := by
  have hKJ : K ≤ J := hKM.trans hMJ
  have htop : ∀ {X : Subgroup (MulAut V)}, K ≤ X → commV X = ⊤ := fun h =>
    top_le_iff.1 (by rw [← hcomm]; exact InternalSec.commV_le_commV h)
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ |
      ⟨G₁, G₂, hsup, -, hc, -, -, W₁, W₂, -, -, -, -, -, hWinf, hp₁, hp₂⟩ |
      ⟨G₁, G₂, t, hJt, -, hc, -, hc₂, -, -, ⟨-, hV12⟩, -, hcV₂, ht₁, ht₂, -⟩ |
      ⟨_, _, -, -, -, -, -, -, hidx, -⟩
  · exact n6_genFitting_eq_of_quasisimple hK hKM hMJ hKn hMn h1.1
  · exact (InternalSec.not_le_perm_three hK hKJ e).elim
  ·
    exfalso
    have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    have hn₁ : ∀ j ∈ J, ∀ g ∈ G₁, j * g * j⁻¹ ∈ G₁ := by
      rw [← hsup]; exact InternalSec.conj_mem_of_mem_sup_of_commute hc
    have hn₂ : ∀ j ∈ J, ∀ g ∈ G₂, j * g * j⁻¹ ∈ G₂ := by
      rw [← hsup, sup_comm]; exact InternalSec.conj_mem_of_mem_sup_of_commute hc'
    have hG₁ : G₁ ≤ J := hsup ▸ le_sup_left
    have hG₂ : G₂ ≤ J := hsup ▸ le_sup_right
    rcases n6_le_or_le hK hKM hMJ hKn hMn hG₁ hG₂ hn₁ hn₂ (hsup.symm ▸ hKJ) with h | h
    · have hW₁ : W₁ = ⊤ :=
        top_le_iff.1 ((htop h).symm.le.trans (InternalSec.commV_le_of_b56Piece hp₁))
      rw [hW₁, top_inf_eq] at hWinf
      rw [hWinf] at hp₂
      exact InternalSec.not_b56Piece_self hp₂
    · have hW₂ : W₂ = ⊤ :=
        top_le_iff.1 ((htop h).symm.le.trans (InternalSec.commV_le_of_b56Piece hp₂))
      rw [hW₂, inf_top_eq] at hWinf
      rw [hWinf] at hp₁
      exact InternalSec.not_b56Piece_self hp₁
  ·
    exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    have htN : t ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup (MulAut V)) : Set (MulAut V)) :=
      InternalSec.mem_normalizer_sup ht₁ ht₂
    have hKN : K ≤ G₁ ⊔ G₂ := by
      rw [hJt] at hKJ
      exact (InternalSec.le_commutator_of_perfect hKJ hK.1).trans
        (InternalSec.commutator_le_of_zpowers htN)
    have hconj : ∀ G' : Subgroup (MulAut V), t ∈ Subgroup.normalizer (G' : Set (MulAut V)) →
        (∀ x ∈ G₁ ⊔ G₂, ∀ g ∈ G', x * g * x⁻¹ ∈ G') → ∀ x ∈ J, ∀ g ∈ G', x * g * x⁻¹ ∈ G' := by
      intro G' ht hN x hx g hg
      rw [hJt] at hx
      obtain ⟨m, hm, s, hs, rfl⟩ :=
        (B19Aux.mem_sup_iff_of_le_normalizer (Subgroup.zpowers_le.2 htN)).1 hx
      have hz : Subgroup.zpowers t ≤ Subgroup.normalizer (G' : Set (MulAut V)) :=
        Subgroup.zpowers_le.2 ht
      have e2 : m * s * g * (m * s)⁻¹ = m * (s * g * s⁻¹) * m⁻¹ := by group
      rw [e2]
      exact hN m hm _ ((Subgroup.mem_normalizer_iff.mp (hz hs) g).mp hg)
    have hn₁ := hconj G₁ ht₁ (InternalSec.conj_mem_of_mem_sup_of_commute hc)
    have hn₂ := hconj G₂ ht₂ (by rw [sup_comm]; exact InternalSec.conj_mem_of_mem_sup_of_commute hc')
    have hG₁ : G₁ ≤ J := by rw [hJt]; exact le_sup_left.trans le_sup_left
    have hG₂ : G₂ ≤ J := by rw [hJt]; exact le_sup_right.trans le_sup_left
    rcases n6_le_or_le hK hKM hMJ hKn hMn hG₁ hG₂ hn₁ hn₂ hKN with h | h
    · rw [htop h, top_inf_eq] at hV12
      rw [hV12, Subgroup.card_bot] at hcV₂
      norm_num at hcV₂
    · exact InternalSec.not_le_of_card_prime hK h hc₂
  ·
    exfalso
    rw [htop hKJ, top_sup_eq, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)

end B56

section Z35Facts

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {Vb : Subgroup X}

omit [Finite X] in
theorem n6_conjAutSub_mul (a b : MulAut X) (L : Subgroup (MulAut X)) :
    conjAutSub a (conjAutSub b L) = conjAutSub (a * b) L := by
  ext x
  simp only [mem_conjAutSub_iff]
  rw [show (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b by group]

omit [Finite X] in
theorem n6_conjAutSub_one (L : Subgroup (MulAut X)) : conjAutSub 1 L = L := by
  ext x
  simp [mem_conjAutSub_iff]

omit [Finite X] in
theorem n6_map_eq_of_mem_stabSub {U : Subgroup X} {g : MulAut X} (hg : g ∈ stabSub U) :
    U.map g.toMonoidHom = U :=
  CFSG.Quasithin.n7_map_eq_of_mem_stabSub hg

omit [Finite X] in
theorem n6_map_map (U : Subgroup X) (a b : MulAut X) :
    (U.map a.toMonoidHom).map b.toMonoidHom = U.map (b * a).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

omit [Finite X] in
theorem n6_commSub_inv {Y : Subgroup X} {K : Subgroup (MulAut X)} {g : MulAut X}
    (hgY : ∀ y ∈ Y, g y ∈ Y) (hgK : g ∈ Subgroup.normalizer (K : Set (MulAut X))) {c : X}
    (hc : c ∈ commSub Y K) : g c ∈ commSub Y K := by
  refine Subgroup.closure_induction (p := fun c _ => g c ∈ commSub Y K) ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨x, hx, w, hw, rfl⟩
    have h1 : g (x w * w⁻¹) = (g * x * g⁻¹) (g w) * (g w)⁻¹ := by
      simp [MulAut.mul_apply]
    rw [h1]
    exact Subgroup.subset_closure ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgK x).mp hx,
      g w, hgY w hw, rfl⟩
  · simp
  · intro a b _ _ ha hb
    rw [map_mul]
    exact (commSub Y K).mul_mem ha hb
  · intro a _ ha
    rw [map_inv]
    exact (commSub Y K).inv_mem ha

variable (h : Z35 Mb Tb Lb Vb)
include h

theorem n6_Tb_le_normalizer : Tb ≤ Subgroup.normalizer (Mb : Set (MulAut X)) := by
  rw [h.Mp_eq]
  exact le_normalizer_conjClosure Lb Tb

theorem n6_conj_mem {t : MulAut X} (ht : t ∈ Tb) {m : MulAut X} (hm : m ∈ Mb) :
    t * m * t⁻¹ ∈ Mb :=
  (Subgroup.mem_normalizer_iff.mp (n6_Tb_le_normalizer h ht) m).mp hm

theorem n6_conj_mem' {t : MulAut X} (ht : t ∈ Tb) {m : MulAut X} (hm : m ∈ Mb) :
    t⁻¹ * m * t ∈ Mb := by
  have := n6_conj_mem h (Tb.inv_mem ht) hm
  simpa using this

theorem n6_inv {m : MulAut X} (hm : m ∈ Mb) {v : X} (hv : v ∈ Vb) : m v ∈ Vb :=
  h.irr.1 ⟨m, hm⟩ v hv

theorem n6_inv_map {t : MulAut X} (ht : t ∈ Tb) {m : MulAut X} (hm : m ∈ Mb) {v : X}
    (hv : v ∈ Vb.map t.toMonoidHom) : m v ∈ Vb.map t.toMonoidHom := by
  obtain ⟨u, hu, rfl⟩ := hv
  refine ⟨(t⁻¹ * m * t) u, n6_inv h (n6_conj_mem' h ht hm) hu, ?_⟩
  simp [MulAut.mul_apply]

theorem n6_stab_map {t : MulAut X} (ht : t ∈ Tb) : Mb ≤ stabSub (Vb.map t.toMonoidHom) :=
  B1.le_stabSub_of_invariant fun _ hm _ hv => n6_inv_map h ht hm hv

theorem n6_irr_map {t : MulAut X} (ht : t ∈ Tb) {U : Subgroup X} (hU : U ≤ Vb.map t.toMonoidHom)
    (hinv : ∀ m ∈ Mb, ∀ u ∈ U, m u ∈ U) : U = ⊥ ∨ U = Vb.map t.toMonoidHom := by
  set U' := U.comap t.toMonoidHom with hU'
  have hU'V : U' ≤ Vb := by
    intro u hu
    obtain ⟨v, hv, hvu⟩ := hU hu
    have : v = u := t.injective hvu
    rw [← this]
    exact hv
  have hU'inv : XMod.IsInv ↥Mb U' := by
    intro m u hu
    show t ((m : MulAut X) u) ∈ U
    have e : t ((m : MulAut X) u) = (t * m * t⁻¹) (t u) := by simp [MulAut.mul_apply]
    rw [e]
    exact hinv _ (n6_conj_mem h ht m.2) _ hu
  rcases h.irr.2.2 U' hU'inv bot_le hU'V with h0 | h0
  · left
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hU hx
    have : v ∈ U' := by show t v ∈ U; exact hx
    rw [h0, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot, this, map_one]
  · right
    refine le_antisymm hU ?_
    rintro _ ⟨v, hv, rfl⟩
    have : v ∈ U' := by rw [h0]; exact hv
    exact this

theorem n6_conj_le {s : MulAut X} (hs : s ∈ Tb) : conjAutSub s Lb ≤ Mb := by
  intro x hx
  rw [mem_conjAutSub_iff] at hx
  rw [h.Mp_eq]
  have := mem_conjClosure (Z := Lb) (H := Tb) hs hx
  simpa [mul_assoc] using this

theorem n6_conj_eq_or_commute {s s' : MulAut X} (hs : s ∈ Tb) (hs' : s' ∈ Tb) :
    conjAutSub s Lb = conjAutSub s' Lb ∨
      ∀ x ∈ conjAutSub s Lb, ∀ y ∈ conjAutSub s' Lb, x * y = y * x := by
  rcases h.comm_conj (s⁻¹ * s') (Tb.mul_mem (Tb.inv_mem hs) hs') with he | hc
  · left
    have e : conjAutSub s' Lb = conjAutSub s (conjAutSub (s⁻¹ * s') Lb) := by
      rw [n6_conjAutSub_mul, mul_inv_cancel_left]
    rw [e, he]
  · right
    intro x hx y hy
    rw [mem_conjAutSub_iff] at hx hy
    have hy' : s⁻¹ * y * s ∈ conjAutSub (s⁻¹ * s') Lb := by
      rw [mem_conjAutSub_iff]
      convert hy using 1
      group
    have hcen := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc) hx
    have e := Subgroup.mem_centralizer_iff.1 hcen _ hy'
    have e2 := congrArg (fun z => s * z * s⁻¹) e
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at e2
    exact e2.symm

theorem n6_Mb_le_normalizer {s : MulAut X} (hs : s ∈ Tb) :
    Mb ≤ Subgroup.normalizer (conjAutSub s Lb : Set (MulAut X)) := by
  rw [h.Mp_eq]
  refine conjClosure_le fun r hr z hz => ?_
  have hx : r * z * r⁻¹ ∈ conjAutSub r Lb := by
    rw [mem_conjAutSub_iff]
    simpa [mul_assoc] using hz
  rcases n6_conj_eq_or_commute h hr hs with he | hc
  · rw [he] at hx
    exact Subgroup.le_normalizer hx
  · exact InternalSec.le_normalizer_of_commute (fun a ha b hb => (hc b hb a ha).symm) hx

theorem n6_conj_normal {s : MulAut X} (hs : s ∈ Tb) {m : MulAut X} (hm : m ∈ Mb) {x : MulAut X}
    (hx : x ∈ conjAutSub s Lb) : m * x * m⁻¹ ∈ conjAutSub s Lb :=
  (Subgroup.mem_normalizer_iff.mp (n6_Mb_le_normalizer h hs hm) x).mp hx

theorem n6_conj_quasi (s : MulAut X) : CFSG.IsQuasisimple ↥(conjAutSub s Lb) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Lb.equivMapOfInjective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective) h.quasi

theorem n6_nontriv_map {s t : MulAut X} (hs : s ∈ Tb) (ht : t ∈ Tb) :
    ∃ l ∈ conjAutSub s Lb, ∃ v ∈ Vb.map t.toMonoidHom, l v ≠ v := by
  obtain ⟨l, hl, v, hv, hlv⟩ := h.nontriv (t⁻¹ * s) (Tb.mul_mem (Tb.inv_mem ht) hs)
  refine ⟨t * l * t⁻¹, ?_, t v, ⟨v, hv, rfl⟩, ?_⟩
  · rw [mem_conjAutSub_iff] at hl ⊢
    convert hl using 1
    group
  · intro e
    apply hlv
    simpa [MulAut.mul_apply] using e

theorem n6_commSub_map {s t : MulAut X} (hs : s ∈ Tb) (ht : t ∈ Tb) :
    commSub (Vb.map t.toMonoidHom) (conjAutSub s Lb) = Vb.map t.toMonoidHom := by
  have hle : commSub (Vb.map t.toMonoidHom) (conjAutSub s Lb) ≤ Vb.map t.toMonoidHom :=
    commSub_le_of_invariant fun x hx v hv => n6_inv_map h ht (n6_conj_le h hs hx) hv
  have hinv : ∀ m ∈ Mb, ∀ u ∈ commSub (Vb.map t.toMonoidHom) (conjAutSub s Lb),
      m u ∈ commSub (Vb.map t.toMonoidHom) (conjAutSub s Lb) := fun m hm u hu =>
    n6_commSub_inv (fun v hv => n6_inv_map h ht hm hv) (n6_Mb_le_normalizer h hs hm) hu
  rcases n6_irr_map h ht hle hinv with h0 | h0
  · exfalso
    obtain ⟨l, hl, v, hv, hlv⟩ := n6_nontriv_map h hs ht
    exact hlv (commSub_eq_bot_iff.1 h0 hv l hl)
  · exact h0

theorem n6_eq_of_map {t t' g : MulAut X} (ht : t ∈ Tb) (ht' : t' ∈ Tb)
    (hg : (Vb.map t.toMonoidHom).map g.toMonoidHom = Vb.map t'.toMonoidHom)
    (hc : ∀ m ∈ Mb, ∀ v ∈ Vb.map t.toMonoidHom, g (m v) = m (g v)) :
    Vb.map t.toMonoidHom = Vb.map t'.toMonoidHom := by
  refine h.homog t ht t' ht'
    ⟨((Vb.map t.toMonoidHom).equivMapOfInjective g.toMonoidHom g.injective).trans
      (MulEquiv.subgroupCongr hg), fun a l l' hl => ?_⟩
  change (a : MulAut X) (g (l : X)) = g (l' : X)
  have hl' : (a : MulAut X) (l : X) = (l' : X) := hl
  rw [← hl']
  exact (hc a a.2 l l.2).symm

theorem n6_schur {t : MulAut X} (ht : t ∈ Tb) {g : MulAut X}
    (hst : ∀ v ∈ Vb.map t.toMonoidHom, g v ∈ Vb.map t.toMonoidHom)
    (hg2 : ∀ v ∈ Vb.map t.toMonoidHom, g (g v) = v)
    (hc : ∀ m ∈ Mb, ∀ v ∈ Vb.map t.toMonoidHom, g (m v) = m (g v)) :
    ∀ v ∈ Vb.map t.toMonoidHom, g v = v := by
  set S := Vb.map t.toMonoidHom with hS
  set F : Subgroup X := S ⊓ MonoidHom.eqLocus g.toMonoidHom (MonoidHom.id X) with hF
  have hFS : F ≤ S := inf_le_left
  have hFinv : ∀ m ∈ Mb, ∀ u ∈ F, m u ∈ F := by
    intro m hm u hu
    refine ⟨n6_inv_map h ht hm hu.1, ?_⟩
    have hu2 : g u = u := hu.2
    show g (m u) = m u
    rw [hc m hm u hu.1, hu2]
  have hinv : ∀ x : X, x⁻¹ = x := fun x =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h.exp x)
  intro v hv
  have hu : g v * v⁻¹ ∈ F := by
    refine ⟨S.mul_mem (hst v hv) (S.inv_mem hv), ?_⟩
    show g (g v * v⁻¹) = g v * v⁻¹
    rw [map_mul, map_inv, hg2 v hv, hinv (g v), hinv v, mul_comm]
  rcases n6_irr_map h ht hFS hFinv with h0 | h0
  · rw [h0, Subgroup.mem_bot, mul_inv_eq_one] at hu
    exact hu
  · have : v ∈ F := by rw [h0]; exact hv
    exact this.2

end Z35Facts

section WFacts

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {Vb : Subgroup X}

omit [Finite X] in
theorem n6_inf_centSub_eq_bot {A : Subgroup (MulAut X)} {W : Subgroup X}
    (hfaith : ∀ a ∈ A, (∀ w ∈ W, a w = w) → a = 1) : A ⊓ centSub W = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  exact Subgroup.mem_bot.2 (hfaith a ha.1 ha.2)

omit [Finite X] in
theorem n6_card_autSub {A : Subgroup (MulAut X)} {W : Subgroup X} (hAW : A ≤ stabSub W)
    (hfaith : ∀ a ∈ A, (∀ w ∈ W, a w = w) → a = 1) : Nat.card (autSub A W) = Nat.card A := by
  have := card_autSub_mul hAW
  rwa [n6_inf_centSub_eq_bot hfaith, Subgroup.card_bot, mul_one] at this

omit [Finite X] in
theorem n6_card_fixV_autSub {A : Subgroup (MulAut X)} {W : Subgroup X} (hAW : A ≤ stabSub W) :
    Nat.card (fixV (autSub A W)) = Nat.card ↥(W ⊓ fixV A) := by
  rw [← map_subtype_fixV_autSub hAW, Subgroup.card_map_of_injective W.subtype_injective]

omit [Finite X] in
theorem n6_autSub_commute {K K' : Subgroup (MulAut X)} {W : Subgroup X}
    (hc : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x) :
    ∀ a ∈ autSub K W, ∀ b ∈ autSub K' W, a * b = b * a := by
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := mem_autSub.1 ha
  obtain ⟨y, hy, rfl⟩ := mem_autSub.1 hb
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc _ hx _ hy)

variable (h : Z35 Mb Tb Lb Vb)
include h

theorem n6_autSub_Mb_le {W : Subgroup X} (hMW : Mb ≤ stabSub W) {P : Subgroup (MulAut ↥W)}
    (hP : ∀ s ∈ Tb, autSub (conjAutSub s Lb) W ≤ P) : autSub Mb W ≤ P := by
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
  have key : Mb ≤ (P.comap (resHom W)).map (stabSub W).subtype := by
    rw [h.Mp_eq]
    refine conjClosure_le fun r hr z hz => ?_
    have hx : r * z * r⁻¹ ∈ conjAutSub r Lb := by
      rw [mem_conjAutSub_iff]
      simpa [mul_assoc] using hz
    have hxs : r * z * r⁻¹ ∈ stabSub W := hMW (n6_conj_le h hr hx)
    exact ⟨⟨_, hxs⟩, hP r hr (mem_autSub.2 ⟨⟨_, hxs⟩, hx, rfl⟩), rfl⟩
  obtain ⟨g', hg', hgg'⟩ := key hg
  have : g' = g := Subtype.ext hgg'
  rw [← this]
  exact hg'

variable {A : Subgroup (MulAut X)} (hA : A ≤ Tb)
include hA

theorem n6_A_le_normalizer : A ≤ Subgroup.normalizer (Mb : Set (MulAut X)) :=
  hA.trans (n6_Tb_le_normalizer h)

theorem n6_W_Mb_stab : Mb ≤ stabSub (orbSup A Vb) := by
  refine B1.le_stabSub_of_invariant fun m hm w hw => ?_
  have hle : orbSup A Vb ≤ (orbSup A Vb).comap m.toMonoidHom := by
    refine orbSup_le fun a ha => ?_
    intro v hv
    exact map_le_orbSup ha (n6_inv_map h (hA ha) hm hv)
  exact hle hw

theorem n6_commSub_W {s : MulAut X} (hs : s ∈ Tb) :
    commSub (orbSup A Vb) (conjAutSub s Lb) = orbSup A Vb := by
  refine le_antisymm (commSub_le_of_invariant fun x hx w hw =>
    ((n6_W_Mb_stab h hA (n6_conj_le h hs hx)) w).2 hw) ?_
  refine orbSup_le fun a ha => ?_
  rw [← n6_commSub_map h hs (hA ha)]
  exact commSub_mono (map_le_orbSup ha) le_rfl

theorem n6_K_quasi {s : MulAut X} (hs : s ∈ Tb) :
    CFSG.IsQuasisimple ↥(autSub (conjAutSub s Lb) (orbSup A Vb)) := by
  refine B1Red.isQuasisimple_of_open (B1Red.isQuasisimple_autSub
    ((n6_conj_le h hs).trans (n6_W_Mb_stab h hA))
    (B1Red.isQuasisimple_to_open (n6_conj_quasi h s)) fun hle => ?_)
  obtain ⟨l, hl, v, hv, hlv⟩ := n6_nontriv_map h hs Tb.one_mem
  exact hlv (hle hl v (map_le_orbSup A.one_mem hv))

theorem n6_K_commV {s : MulAut X} (hs : s ∈ Tb) :
    commV (autSub (conjAutSub s Lb) (orbSup A Vb)) = ⊤ :=
  FFC.B510.commV_autSub_eq_top ((n6_conj_le h hs).trans (n6_W_Mb_stab h hA))
    (n6_commSub_W h hA hs)

omit hA in
theorem n6_K_normal {s : MulAut X} (hs : s ∈ Tb) :
    ∀ m ∈ autSub Mb (orbSup A Vb), ∀ k ∈ autSub (conjAutSub s Lb) (orbSup A Vb),
      m * k * m⁻¹ ∈ autSub (conjAutSub s Lb) (orbSup A Vb) :=
  fun _ hm _ hk => autSub_conj_mem (fun _ hx _ hy => n6_conj_normal h hs hx hy) hm hk

theorem n6_M_normal :
    ∀ g ∈ autSub (Mb ⊔ A) (orbSup A Vb), ∀ m ∈ autSub Mb (orbSup A Vb),
      g * m * g⁻¹ ∈ autSub Mb (orbSup A Vb) := by
  have hn : Mb ⊔ A ≤ Subgroup.normalizer (Mb : Set (MulAut X)) :=
    sup_le Subgroup.le_normalizer (n6_A_le_normalizer h hA)
  exact fun _ hg _ hm => autSub_conj_mem
    (fun _ hx _ hy => (Subgroup.mem_normalizer_iff.mp (hn hx) _).mp hy) hg hm

theorem n6_cent {c : MulAut ↥(orbSup A Vb)} (hc : c ∈ autSub (Mb ⊔ A) (orbSup A Vb))
    (hc2 : c ^ 2 = 1) (hcomm : ∀ k ∈ autSub Mb (orbSup A Vb), c * k = k * c) : c = 1 := by
  have hMW := n6_W_Mb_stab h hA
  obtain ⟨g, hgMA, rfl⟩ := mem_autSub.1 hc
  have hgc : ∀ m ∈ Mb, ∀ w ∈ orbSup A Vb, (g : MulAut X) (m w) = m ((g : MulAut X) w) := by
    intro m hm w hw
    have e := hcomm (resHom (orbSup A Vb) ⟨m, hMW hm⟩) (mem_autSub.2 ⟨⟨m, hMW hm⟩, hm, rfl⟩)
    have := congrArg (fun φ : MulAut ↥(orbSup A Vb) => ((φ ⟨w, hw⟩ : ↥(orbSup A Vb)) : X)) e
    simpa [MulAut.mul_apply, resHom_apply] using this
  have hg2 : ∀ w ∈ orbSup A Vb, (g : MulAut X) ((g : MulAut X) w) = w := by
    intro w hw
    have := congrArg (fun φ : MulAut ↥(orbSup A Vb) => ((φ ⟨w, hw⟩ : ↥(orbSup A Vb)) : X)) hc2
    simpa [pow_two, MulAut.mul_apply, resHom_apply] using this
  obtain ⟨m₀, hm₀, a₀, ha₀, hga⟩ :=
    (B19Aux.mem_sup_iff_of_le_normalizer (n6_A_le_normalizer h hA)).1 hgMA
  have hfixS : ∀ a ∈ A, ∀ v ∈ Vb.map a.toMonoidHom, (g : MulAut X) v = v := by
    intro a ha
    have hSW : Vb.map a.toMonoidHom ≤ orbSup A Vb := map_le_orbSup ha
    have hmap : (Vb.map a.toMonoidHom).map (g : MulAut X).toMonoidHom =
        Vb.map (a₀ * a).toMonoidHom := by
      rw [n6_map_map, hga, mul_assoc, ← n6_map_map]
      exact n6_map_eq_of_mem_stabSub (n6_stab_map h (Tb.mul_mem (hA ha₀) (hA ha)) hm₀)
    have heq := n6_eq_of_map h (hA ha) (Tb.mul_mem (hA ha₀) (hA ha)) hmap
      (fun m hm v hv => hgc m hm v (hSW hv))
    have hst : ∀ v ∈ Vb.map a.toMonoidHom, (g : MulAut X) v ∈ Vb.map a.toMonoidHom := by
      intro v hv
      have : (g : MulAut X) v ∈ (Vb.map a.toMonoidHom).map (g : MulAut X).toMonoidHom :=
        ⟨v, hv, rfl⟩
      rwa [hmap, ← heq] at this
    exact n6_schur h (hA ha) hst (fun v hv => hg2 v (hSW hv))
      (fun m hm v hv => hgc m hm v (hSW hv))
  have hle : orbSup A Vb ≤ MonoidHom.eqLocus (g : MulAut X).toMonoidHom (MonoidHom.id X) :=
    orbSup_le fun a ha v hv => hfixS a ha v hv
  ext w
  have := hle w.2
  simpa [resHom_apply] using this

end WFacts

section SQTK

theorem n6_isQuotientOfSQTK_of_le {G : Type*} [Group G] {M N : Subgroup G} (hNM : N ≤ M)
    (hM : IsQuotientOfSQTKTC ↥M) : IsQuotientOfSQTKTC ↥N := by
  obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := hM
  let N' : Subgroup ↥M := N.subgroupOf M
  refine ⟨↥(N'.comap φ), inferInstance, inferInstance, ?_, hK.subgroup _, ?_⟩
  · intro p hp hp2
    exact (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt (N'.comap φ).subtype
      (N'.comap φ).subtype_injective).trans (hSQT p hp hp2)
  · refine ⟨(Subgroup.subgroupOfEquivOfLe hNM).toMonoidHom.comp (φ.subgroupComap N'), ?_⟩
    exact (Subgroup.subgroupOfEquivOfLe hNM).surjective.comp
      (MonoidHom.subgroupComap_surjective φ N' hφ)

theorem n6_isQuotientOfSQTK_autSub {W : Type} [CommGroup W] {Y M : Subgroup (MulAut W)}
    {U : Subgroup W} (hYM : Y ≤ M) (hM : IsQuotientOfSQTKTC ↥M) :
    IsQuotientOfSQTKTC ↥(autSub Y U) := by
  obtain ⟨S, _, _, h1, h2, φ, hφ⟩ := n6_isQuotientOfSQTK_of_le (inf_le_left.trans hYM :
    Y ⊓ stabSub U ≤ M) hM
  let ρ : ↥(Y ⊓ stabSub U) →* ↥(autSub Y U) :=
    { toFun := fun g => ⟨resHom U ⟨(g : MulAut W), g.2.2⟩,
        mem_autSub.2 ⟨⟨(g : MulAut W), g.2.2⟩, g.2.1, rfl⟩⟩
      map_one' := by ext; rfl
      map_mul' := fun a b => by ext; rfl }
  have hρ : Function.Surjective ρ := by
    rintro ⟨φ', hφ'⟩
    obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ'
    exact ⟨⟨(g : MulAut W), hg, g.2⟩, rfl⟩
  exact ⟨S, inferInstance, inferInstance, h1, h2, ρ.comp φ, hρ.comp hφ⟩

theorem n6_b53_clause {G : Type*} [Group G] (h : IsQuotientOfSQTKTC G) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (N : Subgroup X) (_ : N.Normal),
      SQTKGroup X ∧ Nonempty (G ≃* X ⧸ N) := by
  obtain ⟨S, _, _, hst, hkg, φ, hφ⟩ := h
  exact FFC.b53_clause_of_isQuotientOfSQTKTauCeti
    ⟨S, inferInstance, inferInstance, fun p hp hp2 => hst p hp hp2, hkg, φ, hφ⟩

end SQTK

section Core

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {Vb : Subgroup X}
  (h : Z35 Mb Tb Lb Vb) {A : Subgroup (MulAut X)} (hA : A ≤ Tb)
include h hA

theorem n6_K_sqtk (hA21 : AsA21SQTKSection) {r : MulAut X} (hr : r ∈ Tb) :
    SQTKGroup ↥(autSub (conjAutSub r Lb) (orbSup A Vb)) := by
  obtain ⟨S, _, _, hSQ, hSK, φ, hφ⟩ := h.qsqtk
  have hS : SQTKGroup S := ⟨fun p hp hp2 => hSQ p hp hp2, hSK⟩
  have hLW : conjAutSub r Lb ≤ stabSub (orbSup A Vb) :=
    (n6_conj_le h hr).trans (n6_W_Mb_stab h hA)
  have hLMT : conjAutSub r Lb ≤ Mb ⊔ Tb := (n6_conj_le h hr).trans le_sup_left
  let H : Subgroup S := ((conjAutSub r Lb).subgroupOf (Mb ⊔ Tb)).comap φ
  let ψ : ↥H →* ↥(conjAutSub r Lb) :=
    { toFun := fun x => ⟨((φ x : ↥(Mb ⊔ Tb)) : MulAut X), x.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  let ρ : ↥(conjAutSub r Lb) →* ↥(autSub (conjAutSub r Lb) (orbSup A Vb)) :=
    { toFun := fun g => ⟨resHom (orbSup A Vb) ⟨(g : MulAut X), hLW g.2⟩,
        mem_autSub.2 ⟨⟨_, hLW g.2⟩, g.2, rfl⟩⟩
      map_one' := by ext; rfl
      map_mul' := fun a b => by ext; rfl }
  have hπ : Function.Surjective (ρ.comp ψ) := by
    rintro ⟨k, hk⟩
    obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hk
    obtain ⟨y, hy⟩ := hφ ⟨g, hLMT hg⟩
    refine ⟨⟨y, ?_⟩, ?_⟩
    · show φ y ∈ (conjAutSub r Lb).subgroupOf (Mb ⊔ Tb)
      rw [hy]
      exact hg
    · apply Subtype.ext
      show resHom (orbSup A Vb) ⟨((φ y : ↥(Mb ⊔ Tb)) : MulAut X), _⟩ = resHom (orbSup A Vb) g
      congr 1
      apply Subtype.ext
      simp [hy]
  have hq := n6_K_quasi h hA hr
  have hq' : CFSG.IsQuasisimple ↥(⊤ : Subgroup ↥(autSub (conjAutSub r Lb) (orbSup A Vb))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq
  refine hA21 S hS H _ (ρ.comp ψ) hπ ⊤ (B5.layer_eq_top_of_quasisimple hq') fun g => ⟨0, ?_⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
  rw [pow_zero, pow_one, QuotientGroup.eq_one_iff]
  trivial

theorem n6_core (hB56 : AsB56) (hA21 : AsA21SQTKSection) (hAe : IsElemAbelian2 A) (hAne : A ≠ ⊥)
    (hfaith : ∀ a ∈ A, (∀ w ∈ orbSup A Vb, a w = w) → a = 1)
    (hr : Nat.card ↥(orbSup A Vb) ≤ Nat.card A * Nat.card ↥(orbSup A Vb ⊓ fixV A)) :
    ∃ r ∈ Tb, B51Hyp (ffJ (autSub (Mb ⊔ A) (orbSup A Vb)))
      (autSub (conjAutSub r Lb) (orbSup A Vb)) := by
  have hW2 : ∀ w : ↥(orbSup A Vb), w ^ 2 = 1 := B1.sq_eq_one_sub h.exp _
  have hMG : autSub Mb (orbSup A Vb) ≤ autSub (Mb ⊔ A) (orbSup A Vb) :=
    autSub_mono le_sup_left _
  have hAG : autSub A (orbSup A Vb) ≤ autSub (Mb ⊔ A) (orbSup A Vb) :=
    autSub_mono le_sup_right _
  have hAW : A ≤ stabSub (orbSup A Vb) := le_stabSub_orbSup A Vb
  have hKM : ∀ s ∈ Tb, autSub (conjAutSub s Lb) (orbSup A Vb) ≤ autSub Mb (orbSup A Vb) :=
    fun s hs => autSub_mono (n6_conj_le h hs) _
  have hA2 : IsA2 (autSub (Mb ⊔ A) (orbSup A Vb)) (autSub A (orbSup A Vb)) :=
    B1.isA2_autSub ⟨le_sup_right, hAne, hAe⟩ hAW fun hle => hAne (eq_bot_iff.2 fun a ha =>
      Subgroup.mem_bot.2 (hfaith a ha fun w hw => hle hw a ha))
  have hcard : Nat.card ↥(orbSup A Vb) + 0 ≤
      Nat.card (autSub A (orbSup A Vb)) * Nat.card (fixV (autSub A (orbSup A Vb))) := by
    rw [n6_card_autSub hAW hfaith, n6_card_fixV_autSub hAW, add_zero]
    exact hr
  obtain ⟨B, hBA, hB, -⟩ := B1.exists_offender_below hA2 0 hcard
  set G' := autSub (Mb ⊔ A) (orbSup A Vb) with hG'
  set J := ffJ G' with hJdef
  have hJG : J ≤ G' := B6.ffJ_le G'
  have hJn : ∀ g ∈ G', ∀ j ∈ J, g * j * g⁻¹ ∈ J := fun g hg j hj =>
    (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ G' hg) j).mp hj
  have hBJ : B ≤ J := B6.le_ffJ hB
  have hQ : pCoreOf 2 G' = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQ2 : IsPGroup 2 ↥(pCoreOf 2 G') := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G'
    have hQG : pCoreOf 2 G' ≤ G' := CFSG.LieType.BorelTits.pCoreOf_le 2 G'
    have hQn : ∀ g ∈ G', ∀ q ∈ pCoreOf 2 G', g * q * g⁻¹ ∈ pCoreOf 2 G' :=
      fun g hg q hq => B1Red.conj_mem_pCoreOf hg hq
    have hKQ : ∀ s ∈ Tb, autSub (conjAutSub s Lb) (orbSup A Vb) ≤
        Subgroup.centralizer (pCoreOf 2 G' : Set (MulAut ↥(orbSup A Vb))) := by
      intro s hs k hk
      have hq := n6_K_quasi h hA hs
      rcases n6_le_or_commute hq (hKM s hs) hMG (n6_K_normal h hs) (n6_M_normal h hA) hQG hQn
        with hle | hc
      · exfalso
        have : Group.IsPerfect ↥(autSub (conjAutSub s Lb) (orbSup A Vb)) := hq.1
        have : Nontrivial ↥(autSub (conjAutSub s Lb) (orbSup A Vb)) :=
          CFSG.LocalCores.isQuasisimple_nontrivial hq
        exact Group.IsPerfect.not_isNilpotent _ (hQ2.to_le hle).isNilpotent
      · exact Subgroup.mem_centralizer_iff.2 fun q hq => (hc k hk q hq).symm
    have hMQ := n6_autSub_Mb_le h (n6_W_Mb_stab h hA) hKQ
    by_contra hne
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ2
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.card_eq_one.1 (by simpa using hn))
    have h2 : 2 ∣ Nat.card ↥(pCoreOf 2 G') := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hqd : orderOf q ∣ 2 := by simp [hq]
    have hq2 : (q : MulAut ↥(orbSup A Vb)) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, orderOf_dvd_iff_pow_eq_one.1 hqd, Subgroup.coe_one]
    have hq1 := n6_cent h hA (hQG q.2) hq2 fun k hk =>
      Subgroup.mem_centralizer_iff.1 (hMQ hk) q q.2
    have : q = 1 := Subtype.ext hq1
    rw [this, orderOf_one] at hq
    exact absurd hq (by norm_num)
  have hKJ : ∃ r ∈ Tb, autSub (conjAutSub r Lb) (orbSup A Vb) ≤ J := by
    by_contra hno
    have hKc : ∀ s ∈ Tb, autSub (conjAutSub s Lb) (orbSup A Vb) ≤
        Subgroup.centralizer (J : Set (MulAut ↥(orbSup A Vb))) := by
      intro s hs k hk
      rcases n6_le_or_commute (n6_K_quasi h hA hs) (hKM s hs) hMG (n6_K_normal h hs)
        (n6_M_normal h hA) hJG hJn with hle | hc
      · exact (hno ⟨s, hs, hle⟩).elim
      · exact Subgroup.mem_centralizer_iff.2 fun j hj => (hc k hk j hj).symm
    have hMJ := n6_autSub_Mb_le h (n6_W_Mb_stab h hA) hKc
    obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB.2.1
    apply hb1
    apply Subtype.ext
    exact n6_cent h hA (hAG (hBA b.2)) (hB.2.2.1.2 b b.2) fun k hk =>
      Subgroup.mem_centralizer_iff.1 (hMJ hk) b (hBJ b.2)
  obtain ⟨r, hrT, hKrJ⟩ := hKJ
  have hKq := n6_K_quasi h hA hrT
  have hQJ : pCoreOf 2 J = ⊥ := by
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 J G' hJG
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hJG).2 (B6.le_normalizer_ffJ G'))
    rw [hQ] at this
    exact le_bot_iff.1 this
  have hJsqtk : IsQuotientOfSQTKTC ↥J :=
    n6_isQuotientOfSQTK_of_le hJG (n6_isQuotientOfSQTK_autSub (sup_le_sup_left hA Mb) h.qsqtk)
  have hb53 : B53Hyp J := ⟨hQJ, (InternalSec.ffJ_ffJ _).symm, n6_b53_clause hJsqtk⟩
  have hJne : J ≠ ⊥ := fun hJ0 => hB.2.1 (eq_bot_iff.2 (hJ0 ▸ hBJ))
  have hcases := hB56 ↥(orbSup A Vb) hW2 J hJne hb53
  have hF : quasithinGenFitting J = autSub (conjAutSub r Lb) (orbSup A Vb) :=
    n6_genFitting_eq_of_b56Cases hKq (le_inf (hKM r hrT) hKrJ) inf_le_right
      (fun m hm k hk => n6_K_normal h hrT m hm.1 k hk)
      (fun j hj m hm => ⟨n6_M_normal h hA j (hJG hj) m hm.1,
        J.mul_mem (J.mul_mem hj hm.2) (J.inv_mem hj)⟩)
      (n6_K_commV h hA hrT) hcases
  have hZ : centerOf J ≤ autSub (conjAutSub r Lb) (orbSup A Vb) :=
    hF ▸ InternalSec.centerOf_le_quasithinGenFitting J
  refine ⟨r, hrT, ?_, hKq, n6_K_sqtk h hA hA21 hrT, hKrJ, hQJ, (InternalSec.ffJ_ffJ _).symm⟩
  rw [hF, sup_eq_left.2 hZ]

end Core

section MbEq

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {Vb : Subgroup X}

omit [Finite X] in
theorem n6_exists_res_surj {L : Subgroup (MulAut X)} {W : Subgroup X} (hLW : L ≤ stabSub W) :
    ∃ ρ : ↥L →* ↥(autSub L W), Function.Surjective ρ := by
  let ρ : ↥L →* ↥(autSub L W) :=
    { toFun := fun g => ⟨resHom W ⟨(g : MulAut X), hLW g.2⟩,
        mem_autSub.2 ⟨⟨_, hLW g.2⟩, g.2, rfl⟩⟩
      map_one' := by ext; rfl
      map_mul' := fun a b => by ext; rfl }
  refine ⟨ρ, ?_⟩
  rintro ⟨k, hk⟩
  obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hk
  exact ⟨⟨(g : MulAut X), hg⟩, rfl⟩

omit [Finite X] in
theorem n6_exists_cover {L : Subgroup (MulAut X)} {W : Subgroup X} {r : MulAut X}
    (hLW : conjAutSub r L ≤ stabSub W) :
    ∃ f : ↥L →* ↥(autSub (conjAutSub r L) W), Function.Surjective f := by
  obtain ⟨ρ, hρ⟩ := n6_exists_res_surj hLW
  let e : ↥L ≃* ↥(conjAutSub r L) :=
    L.equivMapOfInjective (MulAut.conj r).toMonoidHom (MulAut.conj r).injective
  exact ⟨ρ.comp e.toMonoidHom, hρ.comp e.surjective⟩

variable (h : Z35 Mb Tb Lb Vb)
include h

theorem n6_Mb_eq_of_forall (hall : ∀ s ∈ Tb, conjAutSub s Lb = Lb) : Mb = Lb := by
  refine le_antisymm ?_ (h.Mp_eq ▸ le_conjClosure Lb Tb)
  rw [h.Mp_eq]
  refine conjClosure_le fun s hs z hz => ?_
  have : s * z * s⁻¹ ∈ conjAutSub s Lb := by
    rw [mem_conjAutSub_iff]
    simpa [mul_assoc] using hz
  rwa [hall s hs] at this

theorem n6_Mb_eq (hB56 : AsB56) (hA21 : AsA21SQTKSection) (i1 : D35InspTwo)
    {A : Subgroup (MulAut X)} (hA : A ≤ Tb) (hAe : IsElemAbelian2 A) (hAne : A ≠ ⊥)
    (hfaith : ∀ a ∈ A, (∀ w ∈ orbSup A Vb, a w = w) → a = 1)
    (hr : Nat.card ↥(orbSup A Vb) ≤ Nat.card A * Nat.card ↥(orbSup A Vb ⊓ fixV A)) : Mb = Lb := by
  obtain ⟨r, hrT, hb51⟩ := n6_core h hA hB56 hA21 hAe hAne hfaith hr
  by_contra hne
  obtain ⟨s, hs, hsne⟩ : ∃ s ∈ Tb, conjAutSub s Lb ≠ Lb := by
    by_contra hall
    exact hne (n6_Mb_eq_of_forall h fun s hs => by_contra fun hs' => hall ⟨s, hs, hs'⟩)
  obtain ⟨r', hr'T, hne'⟩ : ∃ r' ∈ Tb, conjAutSub r Lb ≠ conjAutSub r' Lb := by
    by_cases hrL : conjAutSub r Lb = Lb
    · exact ⟨s, hs, by rw [hrL]; exact fun e => hsne e.symm⟩
    · exact ⟨1, Tb.one_mem, by rw [n6_conjAutSub_one]; exact hrL⟩
  have hc := (n6_conj_eq_or_commute h hrT hr'T).resolve_left hne'
  obtain ⟨f, hf⟩ := n6_exists_cover (L := Lb) ((n6_conj_le h hrT).trans (n6_W_Mb_stab h hA))
  obtain ⟨g, hg⟩ := n6_exists_cover (L := Lb) ((n6_conj_le h hr'T).trans (n6_W_Mb_stab h hA))
  exact i1 ↥(orbSup A Vb) (B1.sq_eq_one_sub h.exp _) _ _ _ hb51 (n6_K_commV h hA hrT)
    (n6_K_quasi h hA hr'T) (n6_autSub_commute hc) (n6_K_commV h hA hr'T)
    ⟨↥Lb, inferInstance, f, g, h.quasi, hf, hg⟩

end MbEq

section Dual

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U : Subgroup V}

theorem n6_transpose_transvection {d : ℕ} {K : Type} [Field K] (i j : Fin d) (c : K) :
    (Matrix.transvection i j c)ᵀ = Matrix.transvection j i c := by
  simp [Matrix.transvection, Matrix.transpose_add]

theorem n6_irr_of_dualNat {d : ℕ} {K : Type} [Field K] (hd : 2 ≤ d)
    {π : ↥(Assembly.LowTwoRank.StatedSL d K) →* ↥L}
    (h : (FFModel.dualNat (Assembly.LowTwoRank.StatedSL d K)).RealizesVia L U ⊥ π) :
    ∀ J : Subgroup V, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → J ≤ U → J = ⊥ ∨ J = U := by
  obtain ⟨f₀, -, hfk, hfe⟩ := FFC.RealizesVia.secMap rfl h
  let f : ↥U →* Multiplicative (Fin d → K) :=
    (FFModel.dualNat (Assembly.LowTwoRank.StatedSL d K)).sec.subtype.comp f₀
  have hfk' : ∀ u : ↥U, f u = 1 ↔ (u : V) ∈ (⊥ : Subgroup V) := fun u => by
    rw [← hfk u]
    exact ⟨fun h1 => Subtype.ext h1, fun h1 => congrArg Subtype.val h1⟩
  have hfe' : ∀ (γ : ↥(Assembly.LowTwoRank.StatedSL d K)) (u : ↥U)
      (hu : ((π γ : ↥L) : MulAut V) (u : V) ∈ U),
      f ⟨_, hu⟩ = dualNatAct (Assembly.LowTwoRank.StatedSL d K) γ (f u) := fun γ u hu => hfe γ u hu
  intro J hJ hJU
  let J' : AddSubgroup (Fin d → K) :=
    { carrier := {v | ∃ u : ↥U, (u : V) ∈ J ∧ f u = Multiplicative.ofAdd v}
      add_mem' := by
        rintro a b ⟨u, hu, hfu⟩ ⟨u', hu', hfu'⟩
        refine ⟨u * u', J.mul_mem hu hu', ?_⟩
        rw [map_mul, hfu, hfu']
        rfl
      zero_mem' := ⟨1, J.one_mem, by simp⟩
      neg_mem' := by
        rintro a ⟨u, hu, hfu⟩
        refine ⟨u⁻¹, J.inv_mem hu, ?_⟩
        rw [map_inv, hfu]
        rfl }
  have hU' : ∀ i j : Fin d, i ≠ j → ∀ c : K, ∀ v ∈ J', Matrix.transvection i j c *ᵥ v ∈ J' := by
    rintro i j hij c v ⟨u, hu, hfu⟩
    set γ : ↥(Assembly.LowTwoRank.StatedSL d K) :=
      ⟨FFC.tGLn j i hij.symm (-c), FFC.tGLn_mem hij.symm (-c)⟩ with hγ
    have hgu : ((π γ : ↥L) : MulAut V) (u : V) ∈ U := h.2.2.2.1 (π γ) u u.2
    refine ⟨⟨_, hgu⟩, hJ _ (π γ).2 u hu, ?_⟩
    rw [hfe' γ u hgu, hfu]
    have hinv : (((γ⁻¹ : ↥(Assembly.LowTwoRank.StatedSL d K)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = Matrix.transvection j i c := by
      rw [Subgroup.coe_inv]
      apply Units.inv_eq_of_mul_eq_one_right
      show Matrix.transvection j i (-c) * Matrix.transvection j i c = 1
      rw [Matrix.transvection_mul_transvection_same j i hij.symm, neg_add_cancel,
        Matrix.transvection_zero]
    show Multiplicative.ofAdd
        ((((γ⁻¹ : ↥(Assembly.LowTwoRank.StatedSL d K)) : GL (Fin d) K) :
          Matrix (Fin d) (Fin d) K)ᵀ *ᵥ Multiplicative.toAdd (Multiplicative.ofAdd v)) = _
    rw [hinv, toAdd_ofAdd, n6_transpose_transvection]
  rcases H.eq_bot_or_eq_top_of_transvection_inv hd J' hU' with h0 | h0
  · left
    refine le_antisymm (fun w hw => ?_) bot_le
    have hwU := hJU hw
    have hmem : Multiplicative.toAdd (f ⟨w, hwU⟩) ∈ J' := ⟨⟨w, hwU⟩, hw, by simp⟩
    rw [h0, AddSubgroup.mem_bot] at hmem
    exact (hfk' _).1 (Multiplicative.toAdd.injective hmem)
  · right
    refine le_antisymm hJU fun w hw => ?_
    have hv : Multiplicative.toAdd (f ⟨w, hw⟩) ∈ J' := by rw [h0]; trivial
    obtain ⟨u', hu', hfu'⟩ := hv
    have h1 : f (⟨w, hw⟩ * u'⁻¹) = 1 := by
      rw [map_mul, map_inv, hfu', ofAdd_toAdd]
      exact mul_inv_cancel _
    have h2 : w * (u' : V)⁻¹ ∈ (⊥ : Subgroup V) := (hfk' _).1 h1
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h2
    rw [h2]
    exact hu'

end Dual

section Proj

variable {Y : Type} [CommGroup Y] {K : Subgroup (MulAut Y)} {U₁ U₂ S₁ S₂ : Subgroup Y}

theorem n6_secIsoL_self (hS : ∀ k ∈ K, ∀ w ∈ S₁, k w ∈ S₁) : SecIsoL K S₁ ⊥ S₁ ⊥ :=
  InternalSec.secIsoL_of_equiv hS hS (MulEquiv.refl _) fun _ _ => rfl

theorem n6_equiv_proj (hsum : U₁ ⊔ U₂ = ⊤) (hinf : U₁ ⊓ U₂ = ⊥)
    (hK₁ : ∀ k ∈ K, ∀ u ∈ U₁, k u ∈ U₁) (hK₂ : ∀ k ∈ K, ∀ u ∈ U₂, k u ∈ U₂)
    (hirr₂ : ∀ J : Subgroup Y, (∀ k ∈ K, ∀ w ∈ J, k w ∈ J) → J ≤ U₂ → J = ⊥ ∨ J = U₂)
    (hS : ∀ k ∈ K, ∀ w ∈ S₁, k w ∈ S₁) (hSne : S₁ ≠ ⊥) (h1 : S₁ ⊓ U₁ = ⊥) :
    ∃ e : ↥S₁ ≃* ↥U₂, ∀ (k : ↥K) (w : ↥S₁),
      ((e ⟨(k : MulAut Y) w, hS k k.2 w w.2⟩ : ↥U₂) : Y) = (k : MulAut Y) (e w : Y) := by
  set p := InternalSec.proj₂ hsum hinf with hp
  have hstab := fun (k : MulAut Y) (hk : k ∈ K) =>
    InternalSec.proj_apply_of_stab hsum hinf (hK₁ k hk) (hK₂ k hk)
  have hinj : ∀ a ∈ S₁, p a = 1 → a = 1 := by
    intro a ha h0
    have ha1 : a ∈ U₁ := by
      have := InternalSec.proj₁_mul_proj₂ hsum hinf a
      rw [← hp, h0, mul_one] at this
      rw [← this]
      exact InternalSec.proj₁_mem hsum hinf a
    have : a ∈ S₁ ⊓ U₁ := ⟨ha, ha1⟩
    rwa [h1, Subgroup.mem_bot] at this
  have himg : S₁.map p = U₂ := by
    have hle : S₁.map p ≤ U₂ := by
      rintro _ ⟨a, -, rfl⟩
      exact InternalSec.proj₂_mem hsum hinf a
    rcases hirr₂ _ (by
      rintro k hk _ ⟨a, ha, rfl⟩
      exact ⟨k a, hS k hk a ha, (hstab k hk a).2⟩) hle with h0 | h0
    · exfalso
      refine hSne (eq_bot_iff.2 fun a ha => ?_)
      have : p a ∈ S₁.map p := ⟨a, ha, rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (hinj a ha this)
    · exact h0
  let f : ↥S₁ →* ↥U₂ := (p.comp S₁.subtype).codRestrict U₂ fun a => InternalSec.proj₂_mem hsum hinf a
  have hf : Function.Bijective f := by
    refine ⟨(injective_iff_map_eq_one _).2 fun a ha =>
      Subtype.ext (hinj a a.2 (congrArg Subtype.val ha)), ?_⟩
    rintro ⟨w, hw⟩
    rw [← himg] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    exact ⟨⟨a, ha⟩, rfl⟩
  exact ⟨MulEquiv.ofBijective f hf, fun k w => (hstab k k.2 w).2⟩

theorem n6_secIsoL_of_stab (hsum : U₁ ⊔ U₂ = ⊤) (hinf : U₁ ⊓ U₂ = ⊥)
    (hK₁ : ∀ k ∈ K, ∀ u ∈ U₁, k u ∈ U₁) (hK₂ : ∀ k ∈ K, ∀ u ∈ U₂, k u ∈ U₂)
    (hirr₁ : ∀ J : Subgroup Y, (∀ k ∈ K, ∀ w ∈ J, k w ∈ J) → J ≤ U₁ → J = ⊥ ∨ J = U₁)
    (hirr₂ : ∀ J : Subgroup Y, (∀ k ∈ K, ∀ w ∈ J, k w ∈ J) → J ≤ U₂ → J = ⊥ ∨ J = U₂)
    (hS₁ : ∀ k ∈ K, ∀ w ∈ S₁, k w ∈ S₁) (hS₂ : ∀ k ∈ K, ∀ w ∈ S₂, k w ∈ S₂)
    (hirrS : ∀ J : Subgroup Y, (∀ k ∈ K, ∀ w ∈ J, k w ∈ J) → J ≤ S₁ → J = ⊥ ∨ J = S₁)
    (hS₁ne : S₁ ≠ ⊥) {a : MulAut Y} (ha : S₁.map a.toMonoidHom = S₂) (haU : a ∈ stabSub U₁) :
    SecIsoL K S₁ ⊥ S₂ ⊥ := by
  by_cases h1 : S₁ ⊓ U₁ = ⊥
  · have h2 : S₂ ⊓ U₁ = ⊥ := by
      rw [eq_bot_iff]
      rintro w ⟨hw2, hw1⟩
      rw [← ha] at hw2
      obtain ⟨s, hs, rfl⟩ := hw2
      have : s ∈ S₁ ⊓ U₁ := ⟨hs, (haU s).1 hw1⟩
      rw [h1, Subgroup.mem_bot] at this
      rw [this, map_one]
      exact Subgroup.one_mem _
    have hS₂ne : S₂ ≠ ⊥ := by
      rw [← ha]
      exact fun h0 => hS₁ne ((Subgroup.map_eq_bot_iff_of_injective _ a.injective).1 h0)
    obtain ⟨e₁, he₁⟩ := n6_equiv_proj hsum hinf hK₁ hK₂ hirr₂ hS₁ hS₁ne h1
    obtain ⟨e₂, he₂⟩ := n6_equiv_proj hsum hinf hK₁ hK₂ hirr₂ hS₂ hS₂ne h2
    refine InternalSec.secIsoL_of_equiv hS₁ hS₂ (e₁.trans e₂.symm) fun k w => ?_
    have hkey : e₂.symm ⟨(k : MulAut Y) (e₁ w), hK₂ k k.2 _ (e₁ w).2⟩ =
        ⟨(k : MulAut Y) (e₂.symm (e₁ w)), hS₂ k k.2 _ (e₂.symm (e₁ w)).2⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [he₂ k (e₂.symm (e₁ w)), MulEquiv.apply_symm_apply]
    have hw : e₁ ⟨(k : MulAut Y) w, hS₁ k k.2 w w.2⟩ = ⟨(k : MulAut Y) (e₁ w), hK₂ k k.2 _ (e₁ w).2⟩ :=
      Subtype.ext (he₁ k w)
    show ((e₂.symm (e₁ ⟨(k : MulAut Y) w, _⟩) : ↥S₂) : Y) = (k : MulAut Y) (e₂.symm (e₁ w) : Y)
    rw [hw, hkey]
  · have hle : S₁ ≤ U₁ := by
      rcases hirrS (S₁ ⊓ U₁) (fun k hk w hw => ⟨hS₁ k hk w hw.1, hK₁ k hk w hw.2⟩) inf_le_left
        with h0 | h0
      · exact (h1 h0).elim
      · rw [← h0]
        exact inf_le_right
    have hSU : S₁ = U₁ := (hirr₁ S₁ hS₁ hle).resolve_left hS₁ne
    have hS₂U : S₂ = U₁ := by
      rw [← ha, hSU]
      exact n6_map_eq_of_mem_stabSub haU
    rw [hS₂U.trans hSU.symm]
    exact n6_secIsoL_self hS₁

end Proj

section Step3

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {Vb : Subgroup X}

omit [Finite X] in
theorem n6_map_one (U : Subgroup X) : U.map (1 : MulAut X).toMonoidHom = U := by
  ext u
  simp

omit [Finite X] in
theorem n6_S_map {W : Subgroup X} {a t : MulAut X} (haW : a ∈ stabSub W)
    (hW : Vb.map t.toMonoidHom ≤ W) :
    ((Vb.map t.toMonoidHom).subgroupOf W).map (resHom W ⟨a, haW⟩).toMonoidHom =
      (Vb.map (a * t).toMonoidHom).subgroupOf W := by
  ext w
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : (s : X) ∈ Vb.map t.toMonoidHom := hs
    obtain ⟨v, hv, hvs⟩ := hs'
    rw [Subgroup.mem_subgroupOf]
    refine ⟨v, hv, ?_⟩
    show a (t v) = a (s : X)
    rw [show t v = (s : X) from hvs]
  · intro hw
    rw [Subgroup.mem_subgroupOf] at hw
    obtain ⟨v, hv, hvw⟩ := hw
    refine ⟨⟨t v, hW ⟨v, hv, rfl⟩⟩, ⟨v, hv, rfl⟩, ?_⟩
    apply Subtype.ext
    exact hvw

omit [Finite X] in
theorem n6_mem_stabSub_of_map_eq {U : Subgroup X} {a : MulAut X}
    (h : U.map a.toMonoidHom = U) : a ∈ stabSub U :=
  CFSG.Quasithin.StabLat.mem_stabSub_of_map_eq h

variable (h : Z35 Mb Tb Lb Vb)
include h

theorem n6_S_inv {W : Subgroup X} {t : MulAut X} (ht : t ∈ Tb) :
    ∀ k ∈ autSub Mb W, ∀ w ∈ (Vb.map t.toMonoidHom).subgroupOf W,
      k w ∈ (Vb.map t.toMonoidHom).subgroupOf W := by
  intro k hk w hw
  obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hk
  rw [Subgroup.mem_subgroupOf] at hw ⊢
  exact n6_inv_map h ht hg hw

theorem n6_S_irr {W : Subgroup X} (hMW : Mb ≤ stabSub W) {t : MulAut X} (ht : t ∈ Tb) :
    ∀ J : Subgroup ↥W, (∀ k ∈ autSub Mb W, ∀ w ∈ J, k w ∈ J) →
      J ≤ (Vb.map t.toMonoidHom).subgroupOf W →
        J = ⊥ ∨ J = (Vb.map t.toMonoidHom).subgroupOf W := by
  intro J hJ hJS
  have hJ' : J.map W.subtype ≤ Vb.map t.toMonoidHom := by
    rintro _ ⟨w, hw, rfl⟩
    exact hJS hw
  have hinv : ∀ m ∈ Mb, ∀ u ∈ J.map W.subtype, m u ∈ J.map W.subtype := by
    rintro m hm _ ⟨w, hw, rfl⟩
    exact ⟨resHom W ⟨m, hMW hm⟩ w, hJ _ (mem_autSub.2 ⟨⟨m, hMW hm⟩, hm, rfl⟩) w hw, rfl⟩
  rcases n6_irr_map h ht hJ' hinv with h0 | h0
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective J W.subtype_injective).1 h0)
  · right
    refine le_antisymm hJS fun w hw => ?_
    have : (w : X) ∈ J.map W.subtype := by rw [h0]; exact hw
    obtain ⟨w', hw', he⟩ := this
    have : w' = w := Subtype.ext he
    rw [← this]
    exact hw'

theorem n6_S_ne_bot {W : Subgroup X} {t : MulAut X} (hW : Vb.map t.toMonoidHom ≤ W) :
    (Vb.map t.toMonoidHom).subgroupOf W ≠ ⊥ := by
  intro h0
  obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.irr.2.1.ne'
  have hmem : (⟨t v, hW ⟨v, hv, rfl⟩⟩ : ↥W) ∈ (Vb.map t.toMonoidHom).subgroupOf W :=
    ⟨v, hv, rfl⟩
  rw [h0, Subgroup.mem_bot] at hmem
  have htv : t v = 1 := congrArg Subtype.val hmem
  apply hv1
  apply Subtype.ext
  simpa using htv

theorem n6_eq_of_secIsoL {W : Subgroup X} (hMW : Mb ≤ stabSub W) {t t' : MulAut X}
    (ht : t ∈ Tb) (ht' : t' ∈ Tb) (hW : Vb.map t.toMonoidHom ≤ W)
    (hW' : Vb.map t'.toMonoidHom ≤ W)
    (hiso : SecIsoL (autSub Mb W) ((Vb.map t.toMonoidHom).subgroupOf W) ⊥
      ((Vb.map t'.toMonoidHom).subgroupOf W) ⊥) :
    Vb.map t.toMonoidHom = Vb.map t'.toMonoidHom := by
  obtain ⟨e, he⟩ := InternalSec.equiv_of_secIsoL hiso
  let E := (Subgroup.subgroupOfEquivOfLe hW).symm
  let E' := (Subgroup.subgroupOfEquivOfLe hW').symm
  refine h.homog t ht t' ht' ⟨E.trans (e.trans E'.symm), fun m l l' hl => ?_⟩
  have hmW : (m : MulAut X) ∈ stabSub W := hMW m.2
  let k : ↥(autSub Mb W) := ⟨resHom W ⟨m, hmW⟩, mem_autSub.2 ⟨⟨m, hmW⟩, m.2, rfl⟩⟩
  have hw : (k : MulAut ↥W) ((E l : ↥((Vb.map t.toMonoidHom).subgroupOf W)) : ↥W) ∈
      (Vb.map t.toMonoidHom).subgroupOf W :=
    n6_S_inv h ht _ k.2 _ (E l).2
  have hw' : (k : MulAut ↥W) ((e (E l) : ↥((Vb.map t'.toMonoidHom).subgroupOf W)) : ↥W) ∈
      (Vb.map t'.toMonoidHom).subgroupOf W :=
    n6_S_inv h ht' _ k.2 _ (e (E l)).2
  have hkey := he k (E l) hw hw'
  have hEl' : (⟨(k : MulAut ↥W) (E l), hw⟩ : ↥((Vb.map t.toMonoidHom).subgroupOf W)) = E l' := by
    apply Subtype.ext
    apply Subtype.ext
    exact hl
  change (m : MulAut X) (((e (E l)) : ↥W) : X) = (((e (E l')) : ↥W) : X)
  rw [← hEl', hkey]
  rfl

theorem n6_A_stab (hB56 : AsB56) (hA21 : AsA21SQTKSection) (hB51 : AsB51) (i2 : D35InspSum)
    {A : Subgroup (MulAut X)} (hA : A ≤ Tb) (hAe : IsElemAbelian2 A) (hAne : A ≠ ⊥)
    (hfaith : ∀ a ∈ A, (∀ w ∈ orbSup A Vb, a w = w) → a = 1)
    (hr : Nat.card ↥(orbSup A Vb) ≤ Nat.card A * Nat.card ↥(orbSup A Vb ⊓ fixV A))
    (hML : Mb = Lb) : A ≤ stabSub Vb := by
  obtain ⟨r, hrT, hb51⟩ := n6_core h hA hB56 hA21 hAe hAne hfaith hr
  have hrL : conjAutSub r Lb = Lb := by
    have h1 := n6_Tb_le_normalizer h hrT
    rw [hML] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp h1
  rw [hrL, ← hML] at hb51
  have hW2 := B1.sq_eq_one_sub h.exp (orbSup A Vb)
  have hMW := n6_W_Mb_stab h hA
  have hAW : A ≤ stabSub (orbSup A Vb) := le_stabSub_orbSup A Vb
  have hcK : commV (autSub Mb (orbSup A Vb)) = ⊤ := by
    have := n6_K_commV h hA Tb.one_mem
    rwa [n6_conjAutSub_one, ← hML] at this
  have hfK : fixV (autSub Mb (orbSup A Vb)) = ⊥ := by
    have := map_subtype_fixV_autSub hMW
    rw [h.fix, inf_bot_eq] at this
    exact (Subgroup.map_eq_bot_iff_of_injective _ (orbSup A Vb).subtype_injective).1 this
  have h3 := (hB51 ↥(orbSup A Vb) hW2 _ _ hb51).2.2.1
  unfold B51Part3 at h3
  rw [hcK, hfK, bot_inf_eq] at h3
  by_contra hAV
  obtain ⟨a, ha, haV⟩ : ∃ a ∈ A, Vb.map a.toMonoidHom ≠ Vb := by
    by_contra hall
    exact hAV fun a ha => n6_mem_stabSub_of_map_eq (by_contra fun hne => hall ⟨a, ha, hne⟩)
  have hW1 : Vb.map (1 : MulAut X).toMonoidHom ≤ orbSup A Vb := map_le_orbSup A.one_mem
  have hWa : Vb.map a.toMonoidHom ≤ orbSup A Vb := map_le_orbSup ha
  have key : ¬ SecIsoL (autSub Mb (orbSup A Vb))
      ((Vb.map (1 : MulAut X).toMonoidHom).subgroupOf (orbSup A Vb)) ⊥
      ((Vb.map a.toMonoidHom).subgroupOf (orbSup A Vb)) ⊥ := fun hiso =>
    haV ((n6_eq_of_secIsoL h hMW Tb.one_mem (hA ha) hW1 hWa hiso).symm.trans (n6_map_one Vb))
  have hirrSec : ∀ t ∈ Tb, Vb.map t.toMonoidHom ≤ orbSup A Vb →
      ⊥ ≤ (Vb.map t.toMonoidHom).subgroupOf (orbSup A Vb) ∧
        (Vb.map t.toMonoidHom).subgroupOf (orbSup A Vb) ≤ ⊤ ∧
        XMod.IsInv ↥(autSub Mb (orbSup A Vb)) ((Vb.map t.toMonoidHom).subgroupOf (orbSup A Vb)) ∧
        XMod.IsIrrSec ↥(autSub Mb (orbSup A Vb)) ⊥
          ((Vb.map t.toMonoidHom).subgroupOf (orbSup A Vb)) := by
    intro t ht hW
    exact ⟨bot_le, le_top, fun k w hw => n6_S_inv h ht k k.2 w hw,
      bot_lt_iff_ne_bot.2 (n6_S_ne_bot h hW),
      fun J hJ _ hJS => n6_S_irr h hMW ht J (fun k hk w hw => hJ ⟨k, hk⟩ w hw) hJS⟩
  rcases h3 with hhom | ⟨n, hn, π, U₁, U₂, hdir, hR₁, hR₂⟩
  · exact key (hhom.2 _ _ (hirrSec 1 Tb.one_mem hW1) (hirrSec a (hA ha) hWa))
  · have hd : 2 ≤ n := by rcases hn with rfl | rfl <;> norm_num
    have hirr₁ := FFC.irr_of_binaryNatural hd
      (⟨ZMod 2, inferInstance, inferInstance, by simp, π, hR₁⟩ :
        BinaryNaturalSL (autSub Mb (orbSup A Vb)) U₁ ⊥ n 1)
    have hirr₂ := n6_irr_of_dualNat hd hR₂
    have hA'e : IsElemAbelian2 (autSub A (orbSup A Vb)) :=
      (B1.isA2_autSub (X := Mb ⊔ A) ⟨le_sup_right, hAne, hAe⟩ hAW fun hle => hAne (eq_bot_iff.2
        fun a ha => Subgroup.mem_bot.2 (hfaith a ha fun w hw => hle hw a ha))).2.2
    have hA'n : autSub A (orbSup A Vb) ≤
        Subgroup.normalizer (autSub Mb (orbSup A Vb) : Set (MulAut ↥(orbSup A Vb))) :=
      le_normalizer_of_conj fun x hx y hy => autSub_conj_mem
        (fun b hb m hm => (Subgroup.mem_normalizer_iff.mp (n6_A_le_normalizer h hA hb) m).mp hm)
        hx hy
    have hnot : ¬ autSub A (orbSup A Vb) ≤ stabSub U₁ := by
      intro hst
      refine key (n6_secIsoL_of_stab hdir.1 hdir.2 (fun k hk u hu => hR₁.2.2.2.1 ⟨k, hk⟩ u hu)
        (fun k hk u hu => hR₂.2.2.2.1 ⟨k, hk⟩ u hu) (fun J hJ hJU => hirr₁ J hJ bot_le hJU)
        hirr₂ (n6_S_inv h Tb.one_mem) (n6_S_inv h (hA ha)) (n6_S_irr h hMW Tb.one_mem)
        (n6_S_ne_bot h hW1) (a := resHom (orbSup A Vb) ⟨a, hAW ha⟩) ?_
        (hst (mem_autSub.2 ⟨⟨a, hAW ha⟩, ha, rfl⟩)))
      rw [n6_S_map (hAW ha) hW1, mul_one]
    have hlt := i2 ↥(orbSup A Vb) _ _ n U₁ U₂ hn hdir ⟨π, hR₁, hR₂⟩ hA'e hA'n hnot
    rw [n6_card_autSub hAW hfaith, n6_card_fixV_autSub hAW] at hlt
    exact absurd hr (not_le.2 hlt)

end Step3

section Main

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {Vb : Subgroup X}

theorem z35_stab (hB56 : AsB56) (hB51 : AsB51) (hA21 : AsA21SQTKSection) (i1 : D35InspTwo)
    (i2 : D35InspSum) (h : Z35 Mb Tb Lb Vb) {A : Subgroup (MulAut X)} (hA : A ≤ Tb)
    (hAe : IsElemAbelian2 A) (hAne : A ≠ ⊥)
    (hfaith : ∀ a ∈ A, (∀ w ∈ orbSup A Vb, a w = w) → a = 1)
    (hr : Nat.card ↥(orbSup A Vb) ≤ Nat.card A * Nat.card ↥(orbSup A Vb ⊓ fixV A)) :
    Mb = Lb ∧ A ≤ stabSub Vb := by
  have hML := n6_Mb_eq h hB56 hA21 i1 hA hAe hAne hfaith hr
  exact ⟨hML, n6_A_stab h hB56 hA21 hB51 i2 hA hAe hAne hfaith hr hML⟩

end Main

end CFSG.Quasithin
