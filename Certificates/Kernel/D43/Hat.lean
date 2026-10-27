module

public import CFSG.Certificates.Kernel.D43.ConjSound
public import CFSG.Milestones.ASVolI.F48.D43.Model
public import Certificates.Kernel.D43.Data
import Certificates.Kernel.D43.Conj
import Certificates.Kernel.D43.Key0
import Certificates.Kernel.D43.Key1
import Certificates.Kernel.D43.Key2
import Certificates.Kernel.D43.Key3
import Certificates.Kernel.D43.Key4
import Certificates.Kernel.D43.Key5
import Certificates.Kernel.D43.Key6
import Certificates.Kernel.D43.Key7
import Certificates.Kernel.D43.Key8
import Certificates.Kernel.D43.RowsA
import Certificates.Kernel.D43.RowsB
import Certificates.Kernel.D43.RowsC
import Certificates.Kernel.D43.Ord
import Certificates.Kernel.D43.Bind

set_option maxRecDepth 400000

public section

open CFSG.ASVolI CFSG.KC.D43 CFSG.KS.ON CFSG.Blueprint.Chevalley

namespace CertificateChecks.KernelD43

theorem exists_ρhat {K : Type} [Field K] (ω : K) (hK : Nat.card K = 27) (hω : ω ^ 3 = ω + 1)
    (h : Fin 9 → ↥(negPerm K))
    (hg : ∀ k : Fin 9, k.val < 8 → ∀ v, (h k : Equiv.Perm (RootModule Tag.D4 K)) v =
      burnsideF48d_genEnd ω k v)
    (hF : ∀ v, (h 8 : Equiv.Perm (RootModule Tag.D4 K)) v = frobV v) :
    ∃ ρ : ↥(Subgroup.closure (Set.range h)) →* Equiv.Perm (Fin 26572),
      (∀ k : Fin 9, k.val < 8 → ∀ p : Fin 26572,
        ((ρ ⟨h k, Subgroup.subset_closure ⟨k, rfl⟩⟩ p : Fin 26572) : ℕ) =
          (burnsideF48d_gen k)[p.val]!) ∧
      ∀ p : Fin 26572, ((ρ ⟨h 8, Subgroup.subset_closure ⟨8, rfl⟩⟩ p : Fin 26572) : ℕ) =
        (burnsideF48d_phi ())[p.val]! := by
  have hrows : ∀ k < 9, rowsOK (RL.getD k []) k = true := by
    intro k hk
    interval_cases k
    exacts [rows0, rows1, rows2, rows3, rows4, rows5, rows6, rows7, rows8]
  have hch : ∀ k < 8, ∀ c < 104, keyChunk KT (RL.getD k []) (tabAt GX.F k) c = true := by
    intro k hk
    interval_cases k
    exacts [keys0, keys1, keys2, keys3, keys4, keys5, keys6, keys7]
  let T : ℕ → ℕ → ℕ := fun k p => if k = 8 then tabAt PX.F 0 p else tabAt GX.F k p
  have hkeys : ∀ k < 9, ∀ p < 26572, T k p < 26572 ∧
      (mv (RL.getD k []) (key KT p) = key KT (T k p) ∨
        mv (RL.getD k []) (key KT p) = vneg (key KT (T k p))) := by
    intro k hk p hp
    by_cases h8 : k = 8
    · subst h8
      exact keyChunks_spec keys8 hp
    · have e : T k = tabAt GX.F k := funext fun q => if_neg h8
      rw [e]
      exact keyChunks_spec (hch k (by omega)) hp
  obtain ⟨hwf, hdist⟩ := ord_spec (O := OT) (ordChunks_spec ordAll)
  obtain ⟨ρ, hρ⟩ := exists_ρhat_of_checks hrows hkeys hwf hdist ω hK hω h hg hF
  refine ⟨ρ, fun k hk p => ?_, fun p => ?_⟩
  · rw [hρ k p, gen_tab hk p.2]
    exact if_neg (by omega)
  · rw [hρ 8 p, phi_tab p.2]
    exact if_pos rfl

theorem rows_all : ∀ k < 9, rowsOK (RL.getD k []) k = true := by
  intro k hk
  interval_cases k
  exacts [rows0, rows1, rows2, rows3, rows4, rows5, rows6, rows7, rows8]

theorem conjW_lt : ∀ k < 8, ∀ i ∈ conjW.getD k [], i < 8 := by decide

theorem frob_facts {K : Type} [Field K] (ω : K) (hK : Nat.card K = 27) (hω : ω ^ 3 = ω + 1)
    (g : Fin 8 → ModGL Tag.D4 K)
    (hg : ∀ k, (g k : Module.End K (RootModule Tag.D4 K)) = burnsideF48d_genEnd ω k) :
    burnsideF48d_frob ^ 3 = 1 ∧ ∀ k < 8, burnsideF48d_frob * burnsideF48d_γ k =
      ((conjW.getD k []).map burnsideF48d_γ).prod * burnsideF48d_frob := by
  haveI : CharP K 3 := by
    haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact charP_of_card_eq_prime_pow (f := 3) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  let h : Fin 9 → ↥(negPerm K) := fun i =>
    if hi : i.val < 8 then glPerm (g ⟨i.val, hi⟩) else frobPerm hK
  have hg' : ∀ k : Fin 9, k.val < 8 → ∀ v, (h k : Equiv.Perm (RootModule Tag.D4 K)) v =
      burnsideF48d_genEnd ω k v := by
    intro k hk v
    change ((if hi : k.val < 8 then glPerm (g ⟨k.val, hi⟩) else frobPerm hK : ↥(negPerm K)) :
      Equiv.Perm (RootModule Tag.D4 K)) v = _
    rw [dif_pos hk, glPerm_apply, hg]
  have hF : ∀ v, (h 8 : Equiv.Perm (RootModule Tag.D4 K)) v = frobV v := by
    intro v
    change ((if hi : (8 : Fin 9).val < 8 then glPerm (g ⟨(8 : Fin 9).val, hi⟩) else frobPerm hK :
      ↥(negPerm K)) : Equiv.Perm (RootModule Tag.D4 K)) v = _
    rw [dif_neg (by decide), frobPerm_apply]
  obtain ⟨ρ, hρg, hρF⟩ := exists_ρhat ω hK hω h hg' hF
  let c : Fin 9 → ↥(Subgroup.closure (Set.range h)) := fun i =>
    ⟨h i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hγ : ∀ k : Fin 9, k.val < 8 → ρ (c k) = burnsideF48d_γ k := by
    intro k hk
    refine (burnsideF48d_perm_eq (burnsideF48d_rep_of_apply ?_ fun p => hρg k hk p)).symm
    simp only [burnsideF48d_gen, CFSG.Monster.B.Co2.Native.hexTable, Array.size_ofFn]
  have hφ : ρ (c 8) = burnsideF48d_frob := by
    refine (burnsideF48d_perm_eq (burnsideF48d_rep_of_apply ?_ fun p => hρF p)).symm
    simp only [burnsideF48d_phi, CFSG.Monster.B.Co2.Native.hexTable, Array.size_ofFn]
  have happ : ∀ (x y : ↥(Subgroup.closure (Set.range h))),
      (∀ v, ((x : ↥(negPerm K)) : Equiv.Perm (RootModule Tag.D4 K)) v =
        ((y : ↥(negPerm K)) : Equiv.Perm (RootModule Tag.D4 K)) v) → x = y :=
    fun x y e => Subtype.ext (Subtype.ext (Equiv.ext e))
  have hmul : ∀ (x y : ↥(Subgroup.closure (Set.range h))) (v : RootModule Tag.D4 K),
      (((x * y : ↥(Subgroup.closure (Set.range h))) : ↥(negPerm K)) :
        Equiv.Perm (RootModule Tag.D4 K)) v =
      ((x : ↥(negPerm K)) : Equiv.Perm (RootModule Tag.D4 K))
        (((y : ↥(negPerm K)) : Equiv.Perm (RootModule Tag.D4 K)) v) := fun _ _ _ => rfl
  let cc : ℕ → ↥(Subgroup.closure (Set.range h)) := fun i => if hi : i < 9 then c ⟨i, hi⟩ else 1
  have hword : ∀ w : List ℕ, (∀ i ∈ w, i < 8) → ∀ v,
      ((((w.map cc).prod : ↥(Subgroup.closure (Set.range h))) : ↥(negPerm K)) :
        Equiv.Perm (RootModule Tag.D4 K)) v = evE ω w v := by
    intro w
    induction w with
    | nil => intro _ v; rfl
    | cons i w ih =>
      intro hw v
      have hi : i < 8 := hw i (List.mem_cons_self ..)
      rw [List.map_cons, List.prod_cons, hmul, ih (fun j hj => hw j (List.mem_cons_of_mem _ hj))]
      have e : cc i = c ⟨i, by omega⟩ := dif_pos (by omega)
      rw [e]
      exact hg' ⟨i, by omega⟩ hi _
  refine ⟨?_, fun k hk => ?_⟩
  · have e3 : c 8 ^ 3 = 1 := by
      refine happ _ _ fun v => ?_
      rw [pow_succ, pow_succ, pow_one, hmul, hmul]
      change frobV (frobV (frobV v)) = v
      exact frobV_cube hK v
    rw [← hφ, ← map_pow, e3, map_one]
  · set w := conjW.getD k [] with hwdef
    have hw := conjW_lt k hk
    have hck : conjOK RL k w = true := List.all_eq_true.1 conj_all k (List.mem_range.2 hk)
    have e : c 8 * c ⟨k, by omega⟩ = (w.map cc).prod * c 8 := by
      refine happ _ _ fun v => ?_
      rw [hmul, hmul, hword w hw]
      change frobV (((h ⟨k, by omega⟩ : ↥(negPerm K)) : Equiv.Perm (RootModule Tag.D4 K)) v) =
        evE ω w (frobV v)
      rw [hg' ⟨k, by omega⟩ hk]
      exact frob_genEnd_of_conjOK ω hω hK rows_all hk hw hck v
    have e2 := congrArg ρ e
    rw [map_mul, map_mul, hφ, hγ ⟨k, by omega⟩ hk, map_list_prod, List.map_map] at e2
    rw [e2]
    congr 2
    refine List.map_congr_left fun i hi => ?_
    have e' : cc i = c ⟨i, by have := hw i hi; omega⟩ := dif_pos (by have := hw i hi; omega)
    change ρ (cc i) = _
    rw [e', hγ ⟨i, _⟩ (hw i hi)]

end CertificateChecks.KernelD43

end
